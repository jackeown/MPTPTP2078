%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MXeDIc4f8h

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:56 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 259 expanded)
%              Number of leaves         :   37 (  92 expanded)
%              Depth                    :   14
%              Number of atoms          :  978 (3647 expanded)
%              Number of equality atoms :   35 ( 123 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t46_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ! [E: $i] :
            ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ B @ D @ C ) )
          <=> ( ( r2_hidden @ E @ A )
              & ( r2_hidden @ ( k1_funct_1 @ D @ E ) @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ! [E: $i] :
              ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ B @ D @ C ) )
            <=> ( ( r2_hidden @ E @ A )
                & ( r2_hidden @ ( k1_funct_1 @ D @ E ) @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t46_funct_2])).

thf('0',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_E_2 ) @ sk_C )
    | ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_E_2 ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( ( k8_relset_1 @ X23 @ X24 @ X22 @ X25 )
        = ( k10_relat_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ X0 )
      = ( k10_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_E_2 @ sk_A )
    | ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_2 @ sk_C ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k10_relat_1 @ X15 @ X13 ) )
      | ( r2_hidden @ ( sk_D_1 @ X15 @ X13 @ X14 ) @ X13 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('9',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_E_2 ) @ sk_C ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('14',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_E_2 ) @ sk_C )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('16',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_2 @ sk_C ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('17',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k10_relat_1 @ X15 @ X13 ) )
      | ( r2_hidden @ ( k4_tarski @ X14 @ ( sk_D_1 @ X15 @ X13 @ X14 ) ) @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('18',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_2 )
      | ( r2_hidden @ ( k4_tarski @ sk_E_2 @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_E_2 ) ) @ sk_D_2 ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['12','13'])).

thf('20',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E_2 @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_E_2 ) ) @ sk_D_2 )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('21',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X16 @ X18 ) @ X17 )
      | ( X18
        = ( k1_funct_1 @ X17 @ X16 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('22',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_2 )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ( ( sk_D_1 @ sk_D_2 @ sk_C @ sk_E_2 )
        = ( k1_funct_1 @ sk_D_2 @ sk_E_2 ) ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['12','13'])).

thf('24',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ( sk_D_1 @ sk_D_2 @ sk_C @ sk_E_2 )
      = ( k1_funct_1 @ sk_D_2 @ sk_E_2 ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_E_2 ) @ sk_C )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C ) ) ),
    inference(demod,[status(thm)],['15','25'])).

thf('27',plain,
    ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_E_2 ) @ sk_C )
    | ~ ( r2_hidden @ sk_E_2 @ sk_A )
    | ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_E_2 ) @ sk_C )
   <= ~ ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_E_2 ) @ sk_C ) ),
    inference(split,[status(esa)],['27'])).

thf('29',plain,
    ( ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_E_2 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,
    ( ~ ( r2_hidden @ sk_E_2 @ sk_A )
    | ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C ) )
    | ~ ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_E_2 ) @ sk_C ) ),
    inference(split,[status(esa)],['27'])).

thf('31',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_E_2 ) @ sk_C )
   <= ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_E_2 ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,
    ( ( r2_hidden @ sk_E_2 @ sk_A )
   <= ( r2_hidden @ sk_E_2 @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('33',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ sk_B ),
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

thf('34',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('35',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('36',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('37',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('38',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('39',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('44',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('45',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['35','42','45'])).

thf('47',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ X17 ) )
      | ( X18
       != ( k1_funct_1 @ X17 @ X16 ) )
      | ( r2_hidden @ ( k4_tarski @ X16 @ X18 ) @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('48',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ( r2_hidden @ ( k4_tarski @ X16 @ ( k1_funct_1 @ X17 @ X16 ) ) @ X17 )
      | ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_D_2 @ X0 ) ) @ sk_D_2 )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ~ ( v1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['12','13'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_D_2 @ X0 ) ) @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E_2 @ ( k1_funct_1 @ sk_D_2 @ sk_E_2 ) ) @ sk_D_2 )
   <= ( r2_hidden @ sk_E_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','52'])).

thf(d14_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k10_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ B )
                  & ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) )).

thf('54',plain,(
    ! [X3: $i,X4: $i,X6: $i,X8: $i,X9: $i] :
      ( ( X6
       != ( k10_relat_1 @ X4 @ X3 ) )
      | ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X4 )
      | ~ ( r2_hidden @ X9 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf('55',plain,(
    ! [X3: $i,X4: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( r2_hidden @ X9 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X4 )
      | ( r2_hidden @ X8 @ ( k10_relat_1 @ X4 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_2 @ X0 ) )
        | ~ ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_E_2 ) @ X0 )
        | ~ ( v1_relat_1 @ sk_D_2 ) )
   <= ( r2_hidden @ sk_E_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['53','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['12','13'])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_2 @ X0 ) )
        | ~ ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_E_2 ) @ X0 ) )
   <= ( r2_hidden @ sk_E_2 @ sk_A ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_2 @ sk_C ) )
   <= ( ( r2_hidden @ sk_E_2 @ sk_A )
      & ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_E_2 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['31','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ X0 )
      = ( k10_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('61',plain,
    ( ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C ) )
   <= ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C ) ) ),
    inference(split,[status(esa)],['27'])).

thf('62',plain,
    ( ~ ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_2 @ sk_C ) )
   <= ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C ) )
    | ~ ( r2_hidden @ sk_E_2 @ sk_A )
    | ~ ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_E_2 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C ) )
    | ( r2_hidden @ sk_E_2 @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('65',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E_2 @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_E_2 ) ) @ sk_D_2 )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('66',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X16 @ X18 ) @ X17 )
      | ( r2_hidden @ X16 @ ( k1_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('67',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_2 )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ( r2_hidden @ sk_E_2 @ ( k1_relat_1 @ sk_D_2 ) ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['12','13'])).

thf('69',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['35','42','45'])).

thf('71',plain,
    ( ( r2_hidden @ sk_E_2 @ sk_A )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C ) ) ),
    inference(demod,[status(thm)],['67','68','69','70'])).

thf('72',plain,
    ( ~ ( r2_hidden @ sk_E_2 @ sk_A )
   <= ~ ( r2_hidden @ sk_E_2 @ sk_A ) ),
    inference(split,[status(esa)],['27'])).

thf('73',plain,
    ( ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C ) )
    | ( r2_hidden @ sk_E_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','29','30','63','64','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MXeDIc4f8h
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:35:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 0.48/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.48/0.71  % Solved by: fo/fo7.sh
% 0.48/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.71  % done 216 iterations in 0.245s
% 0.48/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.48/0.71  % SZS output start Refutation
% 0.48/0.71  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.48/0.71  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.48/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.48/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.48/0.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.48/0.71  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.48/0.71  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.48/0.71  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.48/0.71  thf(sk_E_2_type, type, sk_E_2: $i).
% 0.48/0.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.48/0.71  thf(sk_C_type, type, sk_C: $i).
% 0.48/0.71  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.48/0.71  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.48/0.71  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.48/0.71  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.48/0.71  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.48/0.71  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.48/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.48/0.71  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.48/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.48/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.48/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.71  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.48/0.71  thf(t46_funct_2, conjecture,
% 0.48/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.71     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.48/0.71         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.48/0.71       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.48/0.71         ( ![E:$i]:
% 0.48/0.71           ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ B @ D @ C ) ) <=>
% 0.48/0.71             ( ( r2_hidden @ E @ A ) & 
% 0.48/0.71               ( r2_hidden @ ( k1_funct_1 @ D @ E ) @ C ) ) ) ) ) ))).
% 0.48/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.71    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.71        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.48/0.71            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.48/0.71          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.48/0.71            ( ![E:$i]:
% 0.48/0.71              ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ B @ D @ C ) ) <=>
% 0.48/0.71                ( ( r2_hidden @ E @ A ) & 
% 0.48/0.71                  ( r2_hidden @ ( k1_funct_1 @ D @ E ) @ C ) ) ) ) ) ) )),
% 0.48/0.71    inference('cnf.neg', [status(esa)], [t46_funct_2])).
% 0.48/0.71  thf('0', plain,
% 0.48/0.71      (((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_E_2) @ sk_C)
% 0.48/0.71        | (r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C)))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('1', plain,
% 0.48/0.71      (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C))) | 
% 0.48/0.71       ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_E_2) @ sk_C))),
% 0.48/0.71      inference('split', [status(esa)], ['0'])).
% 0.48/0.71  thf('2', plain,
% 0.48/0.71      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf(redefinition_k8_relset_1, axiom,
% 0.48/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.71       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.48/0.71  thf('3', plain,
% 0.48/0.71      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.48/0.71         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.48/0.71          | ((k8_relset_1 @ X23 @ X24 @ X22 @ X25) = (k10_relat_1 @ X22 @ X25)))),
% 0.48/0.71      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.48/0.71  thf('4', plain,
% 0.48/0.71      (![X0 : $i]:
% 0.48/0.71         ((k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ X0)
% 0.48/0.71           = (k10_relat_1 @ sk_D_2 @ X0))),
% 0.48/0.71      inference('sup-', [status(thm)], ['2', '3'])).
% 0.48/0.71  thf('5', plain,
% 0.48/0.71      (((r2_hidden @ sk_E_2 @ sk_A)
% 0.48/0.71        | (r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C)))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('6', plain,
% 0.48/0.71      (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C)))
% 0.48/0.71         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C))))),
% 0.48/0.71      inference('split', [status(esa)], ['5'])).
% 0.48/0.71  thf('7', plain,
% 0.48/0.71      (((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ sk_C)))
% 0.48/0.71         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C))))),
% 0.48/0.71      inference('sup+', [status(thm)], ['4', '6'])).
% 0.48/0.71  thf(t166_relat_1, axiom,
% 0.48/0.71    (![A:$i,B:$i,C:$i]:
% 0.48/0.71     ( ( v1_relat_1 @ C ) =>
% 0.48/0.71       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.48/0.71         ( ?[D:$i]:
% 0.48/0.71           ( ( r2_hidden @ D @ B ) & 
% 0.48/0.71             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.48/0.71             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.48/0.71  thf('8', plain,
% 0.48/0.71      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.48/0.71         (~ (r2_hidden @ X14 @ (k10_relat_1 @ X15 @ X13))
% 0.48/0.71          | (r2_hidden @ (sk_D_1 @ X15 @ X13 @ X14) @ X13)
% 0.48/0.71          | ~ (v1_relat_1 @ X15))),
% 0.48/0.71      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.48/0.71  thf('9', plain,
% 0.48/0.71      (((~ (v1_relat_1 @ sk_D_2)
% 0.48/0.71         | (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_C @ sk_E_2) @ sk_C)))
% 0.48/0.71         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C))))),
% 0.48/0.71      inference('sup-', [status(thm)], ['7', '8'])).
% 0.48/0.71  thf('10', plain,
% 0.48/0.71      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf(cc2_relat_1, axiom,
% 0.48/0.71    (![A:$i]:
% 0.48/0.71     ( ( v1_relat_1 @ A ) =>
% 0.48/0.71       ( ![B:$i]:
% 0.48/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.48/0.71  thf('11', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]:
% 0.48/0.71         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.48/0.71          | (v1_relat_1 @ X0)
% 0.48/0.71          | ~ (v1_relat_1 @ X1))),
% 0.48/0.71      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.48/0.71  thf('12', plain,
% 0.48/0.71      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D_2))),
% 0.48/0.71      inference('sup-', [status(thm)], ['10', '11'])).
% 0.48/0.71  thf(fc6_relat_1, axiom,
% 0.48/0.71    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.48/0.71  thf('13', plain,
% 0.48/0.71      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 0.48/0.71      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.48/0.71  thf('14', plain, ((v1_relat_1 @ sk_D_2)),
% 0.48/0.71      inference('demod', [status(thm)], ['12', '13'])).
% 0.48/0.71  thf('15', plain,
% 0.48/0.71      (((r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_C @ sk_E_2) @ sk_C))
% 0.48/0.71         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C))))),
% 0.48/0.71      inference('demod', [status(thm)], ['9', '14'])).
% 0.48/0.71  thf('16', plain,
% 0.48/0.71      (((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ sk_C)))
% 0.48/0.71         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C))))),
% 0.48/0.71      inference('sup+', [status(thm)], ['4', '6'])).
% 0.48/0.71  thf('17', plain,
% 0.48/0.71      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.48/0.71         (~ (r2_hidden @ X14 @ (k10_relat_1 @ X15 @ X13))
% 0.48/0.71          | (r2_hidden @ (k4_tarski @ X14 @ (sk_D_1 @ X15 @ X13 @ X14)) @ X15)
% 0.48/0.71          | ~ (v1_relat_1 @ X15))),
% 0.48/0.71      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.48/0.71  thf('18', plain,
% 0.48/0.71      (((~ (v1_relat_1 @ sk_D_2)
% 0.48/0.71         | (r2_hidden @ 
% 0.48/0.71            (k4_tarski @ sk_E_2 @ (sk_D_1 @ sk_D_2 @ sk_C @ sk_E_2)) @ sk_D_2)))
% 0.48/0.71         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C))))),
% 0.48/0.71      inference('sup-', [status(thm)], ['16', '17'])).
% 0.48/0.71  thf('19', plain, ((v1_relat_1 @ sk_D_2)),
% 0.48/0.71      inference('demod', [status(thm)], ['12', '13'])).
% 0.48/0.71  thf('20', plain,
% 0.48/0.71      (((r2_hidden @ 
% 0.48/0.71         (k4_tarski @ sk_E_2 @ (sk_D_1 @ sk_D_2 @ sk_C @ sk_E_2)) @ sk_D_2))
% 0.48/0.71         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C))))),
% 0.48/0.71      inference('demod', [status(thm)], ['18', '19'])).
% 0.48/0.71  thf(t8_funct_1, axiom,
% 0.48/0.71    (![A:$i,B:$i,C:$i]:
% 0.48/0.71     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.48/0.71       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.48/0.71         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.48/0.71           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.48/0.71  thf('21', plain,
% 0.48/0.71      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.48/0.71         (~ (r2_hidden @ (k4_tarski @ X16 @ X18) @ X17)
% 0.48/0.71          | ((X18) = (k1_funct_1 @ X17 @ X16))
% 0.48/0.71          | ~ (v1_funct_1 @ X17)
% 0.48/0.71          | ~ (v1_relat_1 @ X17))),
% 0.48/0.71      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.48/0.71  thf('22', plain,
% 0.48/0.71      (((~ (v1_relat_1 @ sk_D_2)
% 0.48/0.71         | ~ (v1_funct_1 @ sk_D_2)
% 0.48/0.71         | ((sk_D_1 @ sk_D_2 @ sk_C @ sk_E_2) = (k1_funct_1 @ sk_D_2 @ sk_E_2))))
% 0.48/0.71         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C))))),
% 0.48/0.71      inference('sup-', [status(thm)], ['20', '21'])).
% 0.48/0.71  thf('23', plain, ((v1_relat_1 @ sk_D_2)),
% 0.48/0.71      inference('demod', [status(thm)], ['12', '13'])).
% 0.48/0.71  thf('24', plain, ((v1_funct_1 @ sk_D_2)),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('25', plain,
% 0.48/0.71      ((((sk_D_1 @ sk_D_2 @ sk_C @ sk_E_2) = (k1_funct_1 @ sk_D_2 @ sk_E_2)))
% 0.48/0.71         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C))))),
% 0.48/0.71      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.48/0.71  thf('26', plain,
% 0.48/0.71      (((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_E_2) @ sk_C))
% 0.48/0.71         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C))))),
% 0.48/0.71      inference('demod', [status(thm)], ['15', '25'])).
% 0.48/0.71  thf('27', plain,
% 0.48/0.71      ((~ (r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_E_2) @ sk_C)
% 0.48/0.71        | ~ (r2_hidden @ sk_E_2 @ sk_A)
% 0.48/0.71        | ~ (r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C)))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('28', plain,
% 0.48/0.71      ((~ (r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_E_2) @ sk_C))
% 0.48/0.71         <= (~ ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_E_2) @ sk_C)))),
% 0.48/0.71      inference('split', [status(esa)], ['27'])).
% 0.48/0.71  thf('29', plain,
% 0.48/0.71      (~ ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C))) | 
% 0.48/0.71       ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_E_2) @ sk_C))),
% 0.48/0.71      inference('sup-', [status(thm)], ['26', '28'])).
% 0.48/0.71  thf('30', plain,
% 0.48/0.71      (~ ((r2_hidden @ sk_E_2 @ sk_A)) | 
% 0.48/0.71       ~ ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C))) | 
% 0.48/0.71       ~ ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_E_2) @ sk_C))),
% 0.48/0.71      inference('split', [status(esa)], ['27'])).
% 0.48/0.71  thf('31', plain,
% 0.48/0.71      (((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_E_2) @ sk_C))
% 0.48/0.71         <= (((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_E_2) @ sk_C)))),
% 0.48/0.71      inference('split', [status(esa)], ['0'])).
% 0.48/0.71  thf('32', plain,
% 0.48/0.71      (((r2_hidden @ sk_E_2 @ sk_A)) <= (((r2_hidden @ sk_E_2 @ sk_A)))),
% 0.48/0.71      inference('split', [status(esa)], ['5'])).
% 0.48/0.71  thf('33', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ sk_B)),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf(d1_funct_2, axiom,
% 0.48/0.71    (![A:$i,B:$i,C:$i]:
% 0.48/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.71       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.48/0.71           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.48/0.71             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.48/0.71         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.48/0.71           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.48/0.71             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.48/0.71  thf(zf_stmt_1, axiom,
% 0.48/0.71    (![C:$i,B:$i,A:$i]:
% 0.48/0.71     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.48/0.71       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.48/0.71  thf('34', plain,
% 0.48/0.71      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.48/0.71         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 0.48/0.71          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 0.48/0.71          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.48/0.71  thf('35', plain,
% 0.48/0.71      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)
% 0.48/0.71        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_2)))),
% 0.48/0.71      inference('sup-', [status(thm)], ['33', '34'])).
% 0.48/0.71  thf(zf_stmt_2, axiom,
% 0.48/0.71    (![B:$i,A:$i]:
% 0.48/0.71     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.48/0.71       ( zip_tseitin_0 @ B @ A ) ))).
% 0.48/0.71  thf('36', plain,
% 0.48/0.71      (![X29 : $i, X30 : $i]:
% 0.48/0.71         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.48/0.71  thf('37', plain,
% 0.48/0.71      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.48/0.71  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.48/0.71  thf(zf_stmt_5, axiom,
% 0.48/0.71    (![A:$i,B:$i,C:$i]:
% 0.48/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.71       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.48/0.71         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.48/0.71           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.48/0.71             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.48/0.71  thf('38', plain,
% 0.48/0.71      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.48/0.71         (~ (zip_tseitin_0 @ X34 @ X35)
% 0.48/0.71          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 0.48/0.71          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.48/0.71  thf('39', plain,
% 0.48/0.71      (((zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)
% 0.48/0.71        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.48/0.71      inference('sup-', [status(thm)], ['37', '38'])).
% 0.48/0.71  thf('40', plain,
% 0.48/0.71      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A))),
% 0.48/0.71      inference('sup-', [status(thm)], ['36', '39'])).
% 0.48/0.71  thf('41', plain, (((sk_B) != (k1_xboole_0))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('42', plain, ((zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)),
% 0.48/0.71      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 0.48/0.71  thf('43', plain,
% 0.48/0.71      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf(redefinition_k1_relset_1, axiom,
% 0.48/0.71    (![A:$i,B:$i,C:$i]:
% 0.48/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.71       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.48/0.71  thf('44', plain,
% 0.48/0.71      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.48/0.71         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 0.48/0.71          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.48/0.71      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.48/0.71  thf('45', plain,
% 0.48/0.71      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 0.48/0.71      inference('sup-', [status(thm)], ['43', '44'])).
% 0.48/0.71  thf('46', plain, (((sk_A) = (k1_relat_1 @ sk_D_2))),
% 0.48/0.71      inference('demod', [status(thm)], ['35', '42', '45'])).
% 0.48/0.71  thf('47', plain,
% 0.48/0.71      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.48/0.71         (~ (r2_hidden @ X16 @ (k1_relat_1 @ X17))
% 0.48/0.71          | ((X18) != (k1_funct_1 @ X17 @ X16))
% 0.48/0.71          | (r2_hidden @ (k4_tarski @ X16 @ X18) @ X17)
% 0.48/0.71          | ~ (v1_funct_1 @ X17)
% 0.48/0.71          | ~ (v1_relat_1 @ X17))),
% 0.48/0.71      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.48/0.71  thf('48', plain,
% 0.48/0.71      (![X16 : $i, X17 : $i]:
% 0.48/0.71         (~ (v1_relat_1 @ X17)
% 0.48/0.71          | ~ (v1_funct_1 @ X17)
% 0.48/0.71          | (r2_hidden @ (k4_tarski @ X16 @ (k1_funct_1 @ X17 @ X16)) @ X17)
% 0.48/0.71          | ~ (r2_hidden @ X16 @ (k1_relat_1 @ X17)))),
% 0.48/0.71      inference('simplify', [status(thm)], ['47'])).
% 0.48/0.71  thf('49', plain,
% 0.48/0.71      (![X0 : $i]:
% 0.48/0.71         (~ (r2_hidden @ X0 @ sk_A)
% 0.48/0.71          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_D_2 @ X0)) @ sk_D_2)
% 0.48/0.71          | ~ (v1_funct_1 @ sk_D_2)
% 0.48/0.71          | ~ (v1_relat_1 @ sk_D_2))),
% 0.48/0.71      inference('sup-', [status(thm)], ['46', '48'])).
% 0.48/0.71  thf('50', plain, ((v1_funct_1 @ sk_D_2)),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('51', plain, ((v1_relat_1 @ sk_D_2)),
% 0.48/0.71      inference('demod', [status(thm)], ['12', '13'])).
% 0.48/0.71  thf('52', plain,
% 0.48/0.71      (![X0 : $i]:
% 0.48/0.71         (~ (r2_hidden @ X0 @ sk_A)
% 0.48/0.71          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_D_2 @ X0)) @ sk_D_2))),
% 0.48/0.71      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.48/0.71  thf('53', plain,
% 0.48/0.71      (((r2_hidden @ (k4_tarski @ sk_E_2 @ (k1_funct_1 @ sk_D_2 @ sk_E_2)) @ 
% 0.48/0.71         sk_D_2)) <= (((r2_hidden @ sk_E_2 @ sk_A)))),
% 0.48/0.71      inference('sup-', [status(thm)], ['32', '52'])).
% 0.48/0.71  thf(d14_relat_1, axiom,
% 0.48/0.71    (![A:$i]:
% 0.48/0.71     ( ( v1_relat_1 @ A ) =>
% 0.48/0.71       ( ![B:$i,C:$i]:
% 0.48/0.71         ( ( ( C ) = ( k10_relat_1 @ A @ B ) ) <=>
% 0.48/0.71           ( ![D:$i]:
% 0.48/0.71             ( ( r2_hidden @ D @ C ) <=>
% 0.48/0.71               ( ?[E:$i]:
% 0.48/0.71                 ( ( r2_hidden @ E @ B ) & 
% 0.48/0.71                   ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) ) ) ))).
% 0.48/0.71  thf('54', plain,
% 0.48/0.71      (![X3 : $i, X4 : $i, X6 : $i, X8 : $i, X9 : $i]:
% 0.48/0.71         (((X6) != (k10_relat_1 @ X4 @ X3))
% 0.48/0.71          | (r2_hidden @ X8 @ X6)
% 0.48/0.71          | ~ (r2_hidden @ (k4_tarski @ X8 @ X9) @ X4)
% 0.48/0.71          | ~ (r2_hidden @ X9 @ X3)
% 0.48/0.71          | ~ (v1_relat_1 @ X4))),
% 0.48/0.71      inference('cnf', [status(esa)], [d14_relat_1])).
% 0.48/0.71  thf('55', plain,
% 0.48/0.71      (![X3 : $i, X4 : $i, X8 : $i, X9 : $i]:
% 0.48/0.71         (~ (v1_relat_1 @ X4)
% 0.48/0.71          | ~ (r2_hidden @ X9 @ X3)
% 0.48/0.71          | ~ (r2_hidden @ (k4_tarski @ X8 @ X9) @ X4)
% 0.48/0.71          | (r2_hidden @ X8 @ (k10_relat_1 @ X4 @ X3)))),
% 0.48/0.71      inference('simplify', [status(thm)], ['54'])).
% 0.48/0.71  thf('56', plain,
% 0.48/0.71      ((![X0 : $i]:
% 0.48/0.71          ((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ X0))
% 0.48/0.71           | ~ (r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_E_2) @ X0)
% 0.48/0.71           | ~ (v1_relat_1 @ sk_D_2)))
% 0.48/0.71         <= (((r2_hidden @ sk_E_2 @ sk_A)))),
% 0.48/0.71      inference('sup-', [status(thm)], ['53', '55'])).
% 0.48/0.71  thf('57', plain, ((v1_relat_1 @ sk_D_2)),
% 0.48/0.71      inference('demod', [status(thm)], ['12', '13'])).
% 0.48/0.71  thf('58', plain,
% 0.48/0.71      ((![X0 : $i]:
% 0.48/0.71          ((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ X0))
% 0.48/0.71           | ~ (r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_E_2) @ X0)))
% 0.48/0.71         <= (((r2_hidden @ sk_E_2 @ sk_A)))),
% 0.48/0.71      inference('demod', [status(thm)], ['56', '57'])).
% 0.48/0.71  thf('59', plain,
% 0.48/0.71      (((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ sk_C)))
% 0.48/0.71         <= (((r2_hidden @ sk_E_2 @ sk_A)) & 
% 0.48/0.71             ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_E_2) @ sk_C)))),
% 0.48/0.71      inference('sup-', [status(thm)], ['31', '58'])).
% 0.48/0.71  thf('60', plain,
% 0.48/0.71      (![X0 : $i]:
% 0.48/0.71         ((k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ X0)
% 0.48/0.71           = (k10_relat_1 @ sk_D_2 @ X0))),
% 0.48/0.71      inference('sup-', [status(thm)], ['2', '3'])).
% 0.48/0.71  thf('61', plain,
% 0.48/0.71      ((~ (r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C)))
% 0.48/0.71         <= (~
% 0.48/0.71             ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C))))),
% 0.48/0.71      inference('split', [status(esa)], ['27'])).
% 0.48/0.71  thf('62', plain,
% 0.48/0.71      ((~ (r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ sk_C)))
% 0.48/0.71         <= (~
% 0.48/0.71             ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C))))),
% 0.48/0.71      inference('sup-', [status(thm)], ['60', '61'])).
% 0.48/0.71  thf('63', plain,
% 0.48/0.71      (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C))) | 
% 0.48/0.71       ~ ((r2_hidden @ sk_E_2 @ sk_A)) | 
% 0.48/0.71       ~ ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_E_2) @ sk_C))),
% 0.48/0.71      inference('sup-', [status(thm)], ['59', '62'])).
% 0.48/0.71  thf('64', plain,
% 0.48/0.71      (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C))) | 
% 0.48/0.71       ((r2_hidden @ sk_E_2 @ sk_A))),
% 0.48/0.71      inference('split', [status(esa)], ['5'])).
% 0.48/0.71  thf('65', plain,
% 0.48/0.71      (((r2_hidden @ 
% 0.48/0.71         (k4_tarski @ sk_E_2 @ (sk_D_1 @ sk_D_2 @ sk_C @ sk_E_2)) @ sk_D_2))
% 0.48/0.71         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C))))),
% 0.48/0.71      inference('demod', [status(thm)], ['18', '19'])).
% 0.48/0.71  thf('66', plain,
% 0.48/0.71      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.48/0.71         (~ (r2_hidden @ (k4_tarski @ X16 @ X18) @ X17)
% 0.48/0.71          | (r2_hidden @ X16 @ (k1_relat_1 @ X17))
% 0.48/0.71          | ~ (v1_funct_1 @ X17)
% 0.48/0.71          | ~ (v1_relat_1 @ X17))),
% 0.48/0.71      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.48/0.71  thf('67', plain,
% 0.48/0.71      (((~ (v1_relat_1 @ sk_D_2)
% 0.48/0.71         | ~ (v1_funct_1 @ sk_D_2)
% 0.48/0.71         | (r2_hidden @ sk_E_2 @ (k1_relat_1 @ sk_D_2))))
% 0.48/0.71         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C))))),
% 0.48/0.71      inference('sup-', [status(thm)], ['65', '66'])).
% 0.48/0.71  thf('68', plain, ((v1_relat_1 @ sk_D_2)),
% 0.48/0.71      inference('demod', [status(thm)], ['12', '13'])).
% 0.48/0.71  thf('69', plain, ((v1_funct_1 @ sk_D_2)),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('70', plain, (((sk_A) = (k1_relat_1 @ sk_D_2))),
% 0.48/0.71      inference('demod', [status(thm)], ['35', '42', '45'])).
% 0.48/0.71  thf('71', plain,
% 0.48/0.71      (((r2_hidden @ sk_E_2 @ sk_A))
% 0.48/0.71         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C))))),
% 0.48/0.71      inference('demod', [status(thm)], ['67', '68', '69', '70'])).
% 0.48/0.71  thf('72', plain,
% 0.48/0.71      ((~ (r2_hidden @ sk_E_2 @ sk_A)) <= (~ ((r2_hidden @ sk_E_2 @ sk_A)))),
% 0.48/0.71      inference('split', [status(esa)], ['27'])).
% 0.48/0.71  thf('73', plain,
% 0.48/0.71      (~ ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C))) | 
% 0.48/0.71       ((r2_hidden @ sk_E_2 @ sk_A))),
% 0.48/0.71      inference('sup-', [status(thm)], ['71', '72'])).
% 0.48/0.71  thf('74', plain, ($false),
% 0.48/0.71      inference('sat_resolution*', [status(thm)],
% 0.48/0.71                ['1', '29', '30', '63', '64', '73'])).
% 0.48/0.71  
% 0.48/0.71  % SZS output end Refutation
% 0.48/0.71  
% 0.48/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
