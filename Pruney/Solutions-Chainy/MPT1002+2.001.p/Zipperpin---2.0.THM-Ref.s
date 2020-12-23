%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ctNFuv1T4t

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:00 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 207 expanded)
%              Number of leaves         :   33 (  73 expanded)
%              Depth                    :   22
%              Number of atoms          :  897 (2974 expanded)
%              Number of equality atoms :   80 ( 224 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t50_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ C @ A )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( r1_tarski @ C @ ( k8_relset_1 @ A @ B @ D @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r1_tarski @ C @ A )
         => ( ( ( B = k1_xboole_0 )
              & ( A != k1_xboole_0 ) )
            | ( r1_tarski @ C @ ( k8_relset_1 @ A @ B @ D @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_C @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( ( k7_relset_1 @ X13 @ X14 @ X12 @ X15 )
        = ( k9_relat_1 @ X12 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ sk_C @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D @ ( k9_relat_1 @ sk_D @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( ( k8_relset_1 @ X17 @ X18 @ X16 @ X19 )
        = ( k10_relat_1 @ X16 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k10_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_D @ ( k9_relat_1 @ sk_D @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('9',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('11',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['10'])).

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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('13',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('14',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 = X0 )
      | ( zip_tseitin_0 @ X0 @ X3 )
      | ( zip_tseitin_0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('17',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('18',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( sk_B = X1 )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
        | ( zip_tseitin_0 @ X0 @ X1 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,
    ( ! [X1: $i] :
        ( ( zip_tseitin_0 @ k1_xboole_0 @ X1 )
        | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ( X22
        = ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('26',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('28',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('29',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ k1_xboole_0 @ X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_D ) ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','30'])).

thf('32',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( zip_tseitin_0 @ X0 @ X1 )
        | ( zip_tseitin_0 @ X0 @ X2 )
        | ( sk_A
          = ( k1_relat_1 @ sk_D ) ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','31'])).

thf('33',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['20'])).

thf('34',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('37',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['20'])).

thf('38',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ( X22
        = ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('41',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['20'])).

thf('43',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('46',plain,
    ( ( ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X21 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('48',plain,(
    ! [X20: $i] :
      ( zip_tseitin_0 @ X20 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','48'])).

thf('50',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('51',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('52',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D )
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','49','52'])).

thf(t163_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('54',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ ( k1_relat_1 @ X4 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X4 @ X3 ) @ X5 )
      | ( r1_tarski @ X3 @ ( k10_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('55',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
        | ~ ( v1_relat_1 @ sk_D )
        | ~ ( v1_funct_1 @ sk_D )
        | ( r1_tarski @ X0 @ ( k10_relat_1 @ sk_D @ X1 ) )
        | ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ X0 ) @ X1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('57',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('58',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
        | ( r1_tarski @ X0 @ ( k10_relat_1 @ sk_D @ X1 ) )
        | ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ X0 ) @ X1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','58','59'])).

thf('61',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ X0 @ ( k10_relat_1 @ sk_D @ ( k9_relat_1 @ sk_D @ X0 ) ) )
        | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','60'])).

thf('62',plain,
    ( ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_D @ ( k9_relat_1 @ sk_D @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','61'])).

thf('63',plain,(
    ~ ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_D @ ( k9_relat_1 @ sk_D @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('64',plain,(
    sk_A != k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['20'])).

thf('66',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference(simpl_trail,[status(thm)],['32','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( zip_tseitin_0 @ X1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['67'])).

thf('69',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('70',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('72',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ ( k1_relat_1 @ X4 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X4 @ X3 ) @ X5 )
      | ( r1_tarski @ X3 @ ( k10_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( r1_tarski @ X0 @ ( k10_relat_1 @ sk_D @ X1 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['56','57'])).

thf('76',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( r1_tarski @ X0 @ ( k10_relat_1 @ sk_D @ X1 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k10_relat_1 @ sk_D @ ( k9_relat_1 @ sk_D @ X0 ) ) )
      | ~ ( r1_tarski @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','77'])).

thf('79',plain,(
    r1_tarski @ sk_C @ ( k10_relat_1 @ sk_D @ ( k9_relat_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','78'])).

thf('80',plain,(
    $false ),
    inference(demod,[status(thm)],['8','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ctNFuv1T4t
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:47:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.50/0.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.50/0.71  % Solved by: fo/fo7.sh
% 0.50/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.71  % done 236 iterations in 0.243s
% 0.50/0.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.50/0.71  % SZS output start Refutation
% 0.50/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.50/0.71  thf(sk_D_type, type, sk_D: $i).
% 0.50/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.50/0.71  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.50/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.71  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.50/0.71  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.50/0.71  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.50/0.71  thf(sk_C_type, type, sk_C: $i).
% 0.50/0.71  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.50/0.71  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.50/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.50/0.71  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.50/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.50/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.50/0.71  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.50/0.71  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.50/0.71  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.50/0.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.50/0.71  thf(t50_funct_2, conjecture,
% 0.50/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.71     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.50/0.71         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.50/0.71       ( ( r1_tarski @ C @ A ) =>
% 0.50/0.71         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.50/0.71           ( r1_tarski @
% 0.50/0.71             C @ ( k8_relset_1 @ A @ B @ D @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ))).
% 0.50/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.71    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.71        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.50/0.71            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.50/0.71          ( ( r1_tarski @ C @ A ) =>
% 0.50/0.71            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.50/0.71              ( r1_tarski @
% 0.50/0.71                C @ 
% 0.50/0.71                ( k8_relset_1 @ A @ B @ D @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ) )),
% 0.50/0.71    inference('cnf.neg', [status(esa)], [t50_funct_2])).
% 0.50/0.71  thf('0', plain,
% 0.50/0.71      (~ (r1_tarski @ sk_C @ 
% 0.50/0.71          (k8_relset_1 @ sk_A @ sk_B @ sk_D @ 
% 0.50/0.71           (k7_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C)))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('1', plain,
% 0.50/0.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf(redefinition_k7_relset_1, axiom,
% 0.50/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.71       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.50/0.71  thf('2', plain,
% 0.50/0.71      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.50/0.71         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.50/0.71          | ((k7_relset_1 @ X13 @ X14 @ X12 @ X15) = (k9_relat_1 @ X12 @ X15)))),
% 0.50/0.71      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.50/0.71  thf('3', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0) = (k9_relat_1 @ sk_D @ X0))),
% 0.50/0.71      inference('sup-', [status(thm)], ['1', '2'])).
% 0.50/0.71  thf('4', plain,
% 0.50/0.71      (~ (r1_tarski @ sk_C @ 
% 0.50/0.71          (k8_relset_1 @ sk_A @ sk_B @ sk_D @ (k9_relat_1 @ sk_D @ sk_C)))),
% 0.50/0.71      inference('demod', [status(thm)], ['0', '3'])).
% 0.50/0.71  thf('5', plain,
% 0.50/0.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf(redefinition_k8_relset_1, axiom,
% 0.50/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.71       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.50/0.71  thf('6', plain,
% 0.50/0.71      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.50/0.71         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.50/0.71          | ((k8_relset_1 @ X17 @ X18 @ X16 @ X19) = (k10_relat_1 @ X16 @ X19)))),
% 0.50/0.71      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.50/0.71  thf('7', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((k8_relset_1 @ sk_A @ sk_B @ sk_D @ X0) = (k10_relat_1 @ sk_D @ X0))),
% 0.50/0.71      inference('sup-', [status(thm)], ['5', '6'])).
% 0.50/0.71  thf('8', plain,
% 0.50/0.71      (~ (r1_tarski @ sk_C @ (k10_relat_1 @ sk_D @ (k9_relat_1 @ sk_D @ sk_C)))),
% 0.50/0.71      inference('demod', [status(thm)], ['4', '7'])).
% 0.50/0.71  thf('9', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf(d10_xboole_0, axiom,
% 0.50/0.71    (![A:$i,B:$i]:
% 0.50/0.71     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.50/0.71  thf('10', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.50/0.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.50/0.71  thf('11', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.50/0.71      inference('simplify', [status(thm)], ['10'])).
% 0.50/0.71  thf(d1_funct_2, axiom,
% 0.50/0.71    (![A:$i,B:$i,C:$i]:
% 0.50/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.71       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.50/0.71           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.50/0.71             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.50/0.71         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.50/0.71           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.50/0.71             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.50/0.71  thf(zf_stmt_1, axiom,
% 0.50/0.71    (![B:$i,A:$i]:
% 0.50/0.71     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.50/0.71       ( zip_tseitin_0 @ B @ A ) ))).
% 0.50/0.71  thf('12', plain,
% 0.50/0.71      (![X20 : $i, X21 : $i]:
% 0.50/0.71         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.50/0.71  thf('13', plain,
% 0.50/0.71      (![X20 : $i, X21 : $i]:
% 0.50/0.71         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.50/0.71  thf('14', plain,
% 0.50/0.71      (![X20 : $i, X21 : $i]:
% 0.50/0.71         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.50/0.71  thf('15', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.50/0.71         (((X1) = (X0)) | (zip_tseitin_0 @ X0 @ X3) | (zip_tseitin_0 @ X1 @ X2))),
% 0.50/0.71      inference('sup+', [status(thm)], ['13', '14'])).
% 0.50/0.71  thf('16', plain,
% 0.50/0.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.50/0.71  thf(zf_stmt_3, axiom,
% 0.50/0.71    (![C:$i,B:$i,A:$i]:
% 0.50/0.71     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.50/0.71       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.50/0.71  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.50/0.71  thf(zf_stmt_5, axiom,
% 0.50/0.71    (![A:$i,B:$i,C:$i]:
% 0.50/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.71       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.50/0.71         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.50/0.71           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.50/0.71             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.50/0.71  thf('17', plain,
% 0.50/0.71      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.50/0.71         (~ (zip_tseitin_0 @ X25 @ X26)
% 0.50/0.71          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 0.50/0.71          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.50/0.71  thf('18', plain,
% 0.50/0.71      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.50/0.71      inference('sup-', [status(thm)], ['16', '17'])).
% 0.50/0.71  thf('19', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((zip_tseitin_0 @ X1 @ X0)
% 0.50/0.71          | ((sk_B) = (X1))
% 0.50/0.71          | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.50/0.71      inference('sup-', [status(thm)], ['15', '18'])).
% 0.50/0.71  thf('20', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('21', plain,
% 0.50/0.71      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.50/0.71      inference('split', [status(esa)], ['20'])).
% 0.50/0.71  thf('22', plain,
% 0.50/0.71      ((![X0 : $i, X1 : $i]:
% 0.50/0.71          (((X0) != (k1_xboole_0))
% 0.50/0.71           | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.50/0.71           | (zip_tseitin_0 @ X0 @ X1)))
% 0.50/0.71         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.50/0.71      inference('sup-', [status(thm)], ['19', '21'])).
% 0.50/0.71  thf('23', plain,
% 0.50/0.71      ((![X1 : $i]:
% 0.50/0.71          ((zip_tseitin_0 @ k1_xboole_0 @ X1)
% 0.50/0.71           | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)))
% 0.50/0.71         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.50/0.71      inference('simplify', [status(thm)], ['22'])).
% 0.50/0.71  thf('24', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('25', plain,
% 0.50/0.71      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.50/0.71         (~ (v1_funct_2 @ X24 @ X22 @ X23)
% 0.50/0.71          | ((X22) = (k1_relset_1 @ X22 @ X23 @ X24))
% 0.50/0.71          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.50/0.71  thf('26', plain,
% 0.50/0.71      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.50/0.71        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['24', '25'])).
% 0.50/0.71  thf('27', plain,
% 0.50/0.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf(redefinition_k1_relset_1, axiom,
% 0.50/0.71    (![A:$i,B:$i,C:$i]:
% 0.50/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.71       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.50/0.71  thf('28', plain,
% 0.50/0.71      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.50/0.71         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.50/0.71          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.50/0.71      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.50/0.71  thf('29', plain,
% 0.50/0.71      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.50/0.71      inference('sup-', [status(thm)], ['27', '28'])).
% 0.50/0.71  thf('30', plain,
% 0.50/0.71      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.50/0.71      inference('demod', [status(thm)], ['26', '29'])).
% 0.50/0.71  thf('31', plain,
% 0.50/0.71      ((![X0 : $i]:
% 0.50/0.71          ((zip_tseitin_0 @ k1_xboole_0 @ X0) | ((sk_A) = (k1_relat_1 @ sk_D))))
% 0.50/0.71         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.50/0.71      inference('sup-', [status(thm)], ['23', '30'])).
% 0.50/0.71  thf('32', plain,
% 0.50/0.71      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.71          ((zip_tseitin_0 @ X0 @ X1)
% 0.50/0.71           | (zip_tseitin_0 @ X0 @ X2)
% 0.50/0.71           | ((sk_A) = (k1_relat_1 @ sk_D))))
% 0.50/0.71         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.50/0.71      inference('sup+', [status(thm)], ['12', '31'])).
% 0.50/0.71  thf('33', plain,
% 0.50/0.71      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.50/0.71      inference('split', [status(esa)], ['20'])).
% 0.50/0.71  thf('34', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('35', plain,
% 0.50/0.71      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.50/0.71      inference('sup+', [status(thm)], ['33', '34'])).
% 0.50/0.71  thf('36', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.50/0.71      inference('simplify', [status(thm)], ['10'])).
% 0.50/0.71  thf('37', plain,
% 0.50/0.71      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.50/0.71      inference('split', [status(esa)], ['20'])).
% 0.50/0.71  thf('38', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('39', plain,
% 0.50/0.71      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B))
% 0.50/0.71         <= ((((sk_A) = (k1_xboole_0))))),
% 0.50/0.71      inference('sup+', [status(thm)], ['37', '38'])).
% 0.50/0.71  thf('40', plain,
% 0.50/0.71      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.50/0.71         (~ (v1_funct_2 @ X24 @ X22 @ X23)
% 0.50/0.71          | ((X22) = (k1_relset_1 @ X22 @ X23 @ X24))
% 0.50/0.71          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.50/0.71  thf('41', plain,
% 0.50/0.71      (((~ (zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 0.50/0.71         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D))))
% 0.50/0.71         <= ((((sk_A) = (k1_xboole_0))))),
% 0.50/0.71      inference('sup-', [status(thm)], ['39', '40'])).
% 0.50/0.71  thf('42', plain,
% 0.50/0.71      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.50/0.71      inference('split', [status(esa)], ['20'])).
% 0.50/0.71  thf('43', plain,
% 0.50/0.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('44', plain,
% 0.50/0.71      (((m1_subset_1 @ sk_D @ 
% 0.50/0.71         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.50/0.71         <= ((((sk_A) = (k1_xboole_0))))),
% 0.50/0.71      inference('sup+', [status(thm)], ['42', '43'])).
% 0.50/0.71  thf('45', plain,
% 0.50/0.71      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.50/0.71         (~ (zip_tseitin_0 @ X25 @ X26)
% 0.50/0.71          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 0.50/0.71          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.50/0.71  thf('46', plain,
% 0.50/0.71      ((((zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 0.50/0.71         | ~ (zip_tseitin_0 @ sk_B @ k1_xboole_0)))
% 0.50/0.71         <= ((((sk_A) = (k1_xboole_0))))),
% 0.50/0.71      inference('sup-', [status(thm)], ['44', '45'])).
% 0.50/0.71  thf('47', plain,
% 0.50/0.71      (![X20 : $i, X21 : $i]:
% 0.50/0.71         ((zip_tseitin_0 @ X20 @ X21) | ((X21) != (k1_xboole_0)))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.50/0.71  thf('48', plain, (![X20 : $i]: (zip_tseitin_0 @ X20 @ k1_xboole_0)),
% 0.50/0.71      inference('simplify', [status(thm)], ['47'])).
% 0.50/0.71  thf('49', plain,
% 0.50/0.71      (((zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0))
% 0.50/0.71         <= ((((sk_A) = (k1_xboole_0))))),
% 0.50/0.71      inference('demod', [status(thm)], ['46', '48'])).
% 0.50/0.71  thf('50', plain,
% 0.50/0.71      (((m1_subset_1 @ sk_D @ 
% 0.50/0.71         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.50/0.71         <= ((((sk_A) = (k1_xboole_0))))),
% 0.50/0.71      inference('sup+', [status(thm)], ['42', '43'])).
% 0.50/0.71  thf('51', plain,
% 0.50/0.71      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.50/0.71         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.50/0.71          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.50/0.71      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.50/0.71  thf('52', plain,
% 0.50/0.71      ((((k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D) = (k1_relat_1 @ sk_D)))
% 0.50/0.71         <= ((((sk_A) = (k1_xboole_0))))),
% 0.50/0.71      inference('sup-', [status(thm)], ['50', '51'])).
% 0.50/0.71  thf('53', plain,
% 0.50/0.71      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.50/0.71      inference('demod', [status(thm)], ['41', '49', '52'])).
% 0.50/0.71  thf(t163_funct_1, axiom,
% 0.50/0.71    (![A:$i,B:$i,C:$i]:
% 0.50/0.71     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.50/0.71       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 0.50/0.71           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 0.50/0.71         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.50/0.71  thf('54', plain,
% 0.50/0.71      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.50/0.71         (~ (r1_tarski @ X3 @ (k1_relat_1 @ X4))
% 0.50/0.71          | ~ (r1_tarski @ (k9_relat_1 @ X4 @ X3) @ X5)
% 0.50/0.71          | (r1_tarski @ X3 @ (k10_relat_1 @ X4 @ X5))
% 0.50/0.71          | ~ (v1_funct_1 @ X4)
% 0.50/0.71          | ~ (v1_relat_1 @ X4))),
% 0.50/0.71      inference('cnf', [status(esa)], [t163_funct_1])).
% 0.50/0.71  thf('55', plain,
% 0.50/0.71      ((![X0 : $i, X1 : $i]:
% 0.50/0.71          (~ (r1_tarski @ X0 @ k1_xboole_0)
% 0.50/0.71           | ~ (v1_relat_1 @ sk_D)
% 0.50/0.71           | ~ (v1_funct_1 @ sk_D)
% 0.50/0.71           | (r1_tarski @ X0 @ (k10_relat_1 @ sk_D @ X1))
% 0.50/0.71           | ~ (r1_tarski @ (k9_relat_1 @ sk_D @ X0) @ X1)))
% 0.50/0.71         <= ((((sk_A) = (k1_xboole_0))))),
% 0.50/0.71      inference('sup-', [status(thm)], ['53', '54'])).
% 0.50/0.71  thf('56', plain,
% 0.50/0.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf(cc1_relset_1, axiom,
% 0.50/0.71    (![A:$i,B:$i,C:$i]:
% 0.50/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.71       ( v1_relat_1 @ C ) ))).
% 0.50/0.71  thf('57', plain,
% 0.50/0.71      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.50/0.71         ((v1_relat_1 @ X6)
% 0.50/0.71          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.50/0.71      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.50/0.71  thf('58', plain, ((v1_relat_1 @ sk_D)),
% 0.50/0.71      inference('sup-', [status(thm)], ['56', '57'])).
% 0.50/0.71  thf('59', plain, ((v1_funct_1 @ sk_D)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('60', plain,
% 0.50/0.71      ((![X0 : $i, X1 : $i]:
% 0.50/0.71          (~ (r1_tarski @ X0 @ k1_xboole_0)
% 0.50/0.71           | (r1_tarski @ X0 @ (k10_relat_1 @ sk_D @ X1))
% 0.50/0.71           | ~ (r1_tarski @ (k9_relat_1 @ sk_D @ X0) @ X1)))
% 0.50/0.71         <= ((((sk_A) = (k1_xboole_0))))),
% 0.50/0.71      inference('demod', [status(thm)], ['55', '58', '59'])).
% 0.50/0.71  thf('61', plain,
% 0.50/0.71      ((![X0 : $i]:
% 0.50/0.71          ((r1_tarski @ X0 @ (k10_relat_1 @ sk_D @ (k9_relat_1 @ sk_D @ X0)))
% 0.50/0.71           | ~ (r1_tarski @ X0 @ k1_xboole_0)))
% 0.50/0.71         <= ((((sk_A) = (k1_xboole_0))))),
% 0.50/0.71      inference('sup-', [status(thm)], ['36', '60'])).
% 0.50/0.71  thf('62', plain,
% 0.50/0.71      (((r1_tarski @ sk_C @ (k10_relat_1 @ sk_D @ (k9_relat_1 @ sk_D @ sk_C))))
% 0.50/0.71         <= ((((sk_A) = (k1_xboole_0))))),
% 0.50/0.71      inference('sup-', [status(thm)], ['35', '61'])).
% 0.50/0.71  thf('63', plain,
% 0.50/0.71      (~ (r1_tarski @ sk_C @ (k10_relat_1 @ sk_D @ (k9_relat_1 @ sk_D @ sk_C)))),
% 0.50/0.71      inference('demod', [status(thm)], ['4', '7'])).
% 0.50/0.71  thf('64', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['62', '63'])).
% 0.50/0.71  thf('65', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.50/0.71      inference('split', [status(esa)], ['20'])).
% 0.50/0.71  thf('66', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.50/0.71      inference('sat_resolution*', [status(thm)], ['64', '65'])).
% 0.50/0.71  thf('67', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.71         ((zip_tseitin_0 @ X0 @ X1)
% 0.50/0.71          | (zip_tseitin_0 @ X0 @ X2)
% 0.50/0.71          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.50/0.71      inference('simpl_trail', [status(thm)], ['32', '66'])).
% 0.50/0.71  thf('68', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         (((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_0 @ X1 @ X0))),
% 0.50/0.71      inference('condensation', [status(thm)], ['67'])).
% 0.50/0.71  thf('69', plain,
% 0.50/0.71      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.50/0.71      inference('sup-', [status(thm)], ['16', '17'])).
% 0.50/0.71  thf('70', plain,
% 0.50/0.71      ((((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.50/0.71      inference('sup-', [status(thm)], ['68', '69'])).
% 0.50/0.71  thf('71', plain,
% 0.50/0.71      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.50/0.71      inference('demod', [status(thm)], ['26', '29'])).
% 0.50/0.71  thf('72', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.50/0.71      inference('clc', [status(thm)], ['70', '71'])).
% 0.50/0.71  thf('73', plain,
% 0.50/0.71      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.50/0.71         (~ (r1_tarski @ X3 @ (k1_relat_1 @ X4))
% 0.50/0.71          | ~ (r1_tarski @ (k9_relat_1 @ X4 @ X3) @ X5)
% 0.50/0.71          | (r1_tarski @ X3 @ (k10_relat_1 @ X4 @ X5))
% 0.50/0.71          | ~ (v1_funct_1 @ X4)
% 0.50/0.71          | ~ (v1_relat_1 @ X4))),
% 0.50/0.71      inference('cnf', [status(esa)], [t163_funct_1])).
% 0.50/0.71  thf('74', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         (~ (r1_tarski @ X0 @ sk_A)
% 0.50/0.71          | ~ (v1_relat_1 @ sk_D)
% 0.50/0.71          | ~ (v1_funct_1 @ sk_D)
% 0.50/0.71          | (r1_tarski @ X0 @ (k10_relat_1 @ sk_D @ X1))
% 0.50/0.71          | ~ (r1_tarski @ (k9_relat_1 @ sk_D @ X0) @ X1))),
% 0.50/0.71      inference('sup-', [status(thm)], ['72', '73'])).
% 0.50/0.71  thf('75', plain, ((v1_relat_1 @ sk_D)),
% 0.50/0.71      inference('sup-', [status(thm)], ['56', '57'])).
% 0.50/0.71  thf('76', plain, ((v1_funct_1 @ sk_D)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('77', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         (~ (r1_tarski @ X0 @ sk_A)
% 0.50/0.71          | (r1_tarski @ X0 @ (k10_relat_1 @ sk_D @ X1))
% 0.50/0.71          | ~ (r1_tarski @ (k9_relat_1 @ sk_D @ X0) @ X1))),
% 0.50/0.71      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.50/0.71  thf('78', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((r1_tarski @ X0 @ (k10_relat_1 @ sk_D @ (k9_relat_1 @ sk_D @ X0)))
% 0.50/0.71          | ~ (r1_tarski @ X0 @ sk_A))),
% 0.50/0.71      inference('sup-', [status(thm)], ['11', '77'])).
% 0.50/0.71  thf('79', plain,
% 0.50/0.71      ((r1_tarski @ sk_C @ (k10_relat_1 @ sk_D @ (k9_relat_1 @ sk_D @ sk_C)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['9', '78'])).
% 0.50/0.71  thf('80', plain, ($false), inference('demod', [status(thm)], ['8', '79'])).
% 0.50/0.71  
% 0.50/0.71  % SZS output end Refutation
% 0.50/0.71  
% 0.50/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
