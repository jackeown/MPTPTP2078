%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mk2mR4k8yH

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:22 EST 2020

% Result     : Theorem 0.88s
% Output     : Refutation 0.88s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 140 expanded)
%              Number of leaves         :   45 (  62 expanded)
%              Depth                    :   23
%              Number of atoms          :  720 (1288 expanded)
%              Number of equality atoms :   52 (  75 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('0',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ ( sk_B @ X14 ) @ X14 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r2_hidden @ X19 @ X20 )
      | ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

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

thf('3',plain,(
    ! [X44: $i,X45: $i] :
      ( ( zip_tseitin_0 @ X44 @ X45 )
      | ( X44 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( zip_tseitin_0 @ X49 @ X50 )
      | ( zip_tseitin_1 @ X51 @ X49 @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X49 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( zip_tseitin_1 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf(t61_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )).

thf(zf_stmt_5,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_funct_2])).

thf('8',plain,(
    v1_funct_2 @ sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(t56_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ! [B: $i,C: $i] :
            ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
       => ( A = k1_xboole_0 ) ) ) )).

thf('9',plain,(
    ! [X24: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ X24 ) @ ( sk_C @ X24 ) ) @ X24 )
      | ( X24 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t56_relat_1])).

thf('10',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('11',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ( r2_hidden @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ sk_C_1 ) @ ( sk_C @ sk_C_1 ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('15',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v1_relat_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('16',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ sk_C_1 ) @ ( sk_C @ sk_C_1 ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf(t128_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) )
    <=> ( ( A = C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('18',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X10 = X9 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X9 ) @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('19',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( sk_B_1 @ sk_C_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X24: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ X24 ) @ ( sk_C @ X24 ) ) @ X24 )
      | ( X24 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t56_relat_1])).

thf('21',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C @ sk_C_1 ) ) @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('23',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C @ sk_C_1 ) ) @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C @ sk_C_1 ) ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('25',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X28 @ X30 ) @ X29 )
      | ( X30
        = ( k1_funct_1 @ X29 @ X28 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('26',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( sk_C @ sk_C_1 )
      = ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('28',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('29',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( sk_C @ sk_C_1 )
      = ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('31',plain,
    ( ~ ( r2_hidden @ ( sk_C @ sk_C_1 ) @ sk_B_2 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ sk_C_1 ) @ ( sk_C @ sk_C_1 ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('33',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X9 ) @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('34',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C @ sk_C_1 ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['31','34'])).

thf('36',plain,(
    v1_funct_2 @ k1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_2 ),
    inference(demod,[status(thm)],['8','35'])).

thf('37',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( v1_funct_2 @ X48 @ X46 @ X47 )
      | ( X46
        = ( k1_relset_1 @ X46 @ X47 @ X48 ) )
      | ~ ( zip_tseitin_1 @ X48 @ X47 @ X46 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('38',plain,
    ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ sk_B_2 @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','38'])).

thf('40',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('41',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t22_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) )
      <=> ( ( k1_relset_1 @ B @ A @ C )
          = B ) ) ) )).

thf('43',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( ( k1_relset_1 @ X39 @ X40 @ X41 )
       != X39 )
      | ~ ( r2_hidden @ X42 @ X39 )
      | ( r2_hidden @ ( k4_tarski @ X42 @ ( sk_E @ X42 @ X41 ) ) @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[t22_relset_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_E @ X2 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
       != X1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ ( sk_E @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ k1_xboole_0 ) ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','46'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('48',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(fc3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ A @ B ) ) )).

thf('49',plain,(
    ! [X7: $i,X8: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc3_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ ( sk_E @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ k1_xboole_0 ) ) @ k1_xboole_0 ),
    inference(clc,[status(thm)],['47','50'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('52',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ X31 @ X32 )
      | ~ ( r1_tarski @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('53',plain,(
    ~ ( r1_tarski @ k1_xboole_0 @ ( k4_tarski @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ ( sk_E @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['53','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.15/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.17  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mk2mR4k8yH
% 0.18/0.38  % Computer   : n009.cluster.edu
% 0.18/0.38  % Model      : x86_64 x86_64
% 0.18/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.18/0.38  % Memory     : 8042.1875MB
% 0.18/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.18/0.38  % CPULimit   : 60
% 0.18/0.38  % DateTime   : Tue Dec  1 20:06:26 EST 2020
% 0.18/0.38  % CPUTime    : 
% 0.18/0.38  % Running portfolio for 600 s
% 0.18/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.18/0.38  % Number of cores: 8
% 0.18/0.39  % Python version: Python 3.6.8
% 0.18/0.39  % Running in FO mode
% 0.88/1.07  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.88/1.07  % Solved by: fo/fo7.sh
% 0.88/1.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.88/1.07  % done 593 iterations in 0.577s
% 0.88/1.07  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.88/1.07  % SZS output start Refutation
% 0.88/1.07  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.88/1.07  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.88/1.07  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.88/1.07  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.88/1.07  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.88/1.07  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.88/1.07  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.88/1.07  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.88/1.07  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.88/1.07  thf(sk_B_type, type, sk_B: $i > $i).
% 0.88/1.07  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.88/1.07  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.88/1.07  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.88/1.07  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.88/1.07  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.88/1.07  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.88/1.07  thf(sk_C_type, type, sk_C: $i > $i).
% 0.88/1.07  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.88/1.07  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.88/1.07  thf(sk_A_type, type, sk_A: $i).
% 0.88/1.07  thf(sk_E_type, type, sk_E: $i > $i > $i).
% 0.88/1.07  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.88/1.07  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.88/1.07  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.88/1.07  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.88/1.07  thf(existence_m1_subset_1, axiom,
% 0.88/1.07    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.88/1.07  thf('0', plain, (![X14 : $i]: (m1_subset_1 @ (sk_B @ X14) @ X14)),
% 0.88/1.07      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.88/1.07  thf(t2_subset, axiom,
% 0.88/1.07    (![A:$i,B:$i]:
% 0.88/1.07     ( ( m1_subset_1 @ A @ B ) =>
% 0.88/1.07       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.88/1.07  thf('1', plain,
% 0.88/1.07      (![X19 : $i, X20 : $i]:
% 0.88/1.07         ((r2_hidden @ X19 @ X20)
% 0.88/1.07          | (v1_xboole_0 @ X20)
% 0.88/1.07          | ~ (m1_subset_1 @ X19 @ X20))),
% 0.88/1.07      inference('cnf', [status(esa)], [t2_subset])).
% 0.88/1.07  thf('2', plain,
% 0.88/1.07      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.88/1.07      inference('sup-', [status(thm)], ['0', '1'])).
% 0.88/1.07  thf(d1_funct_2, axiom,
% 0.88/1.07    (![A:$i,B:$i,C:$i]:
% 0.88/1.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.88/1.07       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.88/1.07           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.88/1.07             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.88/1.07         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.88/1.07           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.88/1.07             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.88/1.07  thf(zf_stmt_0, axiom,
% 0.88/1.07    (![B:$i,A:$i]:
% 0.88/1.07     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.88/1.07       ( zip_tseitin_0 @ B @ A ) ))).
% 0.88/1.07  thf('3', plain,
% 0.88/1.07      (![X44 : $i, X45 : $i]:
% 0.88/1.07         ((zip_tseitin_0 @ X44 @ X45) | ((X44) = (k1_xboole_0)))),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.07  thf(t4_subset_1, axiom,
% 0.88/1.07    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.88/1.07  thf('4', plain,
% 0.88/1.07      (![X18 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X18))),
% 0.88/1.07      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.88/1.07  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.88/1.07  thf(zf_stmt_2, axiom,
% 0.88/1.07    (![C:$i,B:$i,A:$i]:
% 0.88/1.07     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.88/1.07       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.88/1.07  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.88/1.07  thf(zf_stmt_4, axiom,
% 0.88/1.07    (![A:$i,B:$i,C:$i]:
% 0.88/1.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.88/1.07       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.88/1.07         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.88/1.07           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.88/1.07             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.88/1.07  thf('5', plain,
% 0.88/1.07      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.88/1.07         (~ (zip_tseitin_0 @ X49 @ X50)
% 0.88/1.07          | (zip_tseitin_1 @ X51 @ X49 @ X50)
% 0.88/1.07          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X49))))),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.88/1.07  thf('6', plain,
% 0.88/1.07      (![X0 : $i, X1 : $i]:
% 0.88/1.07         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 0.88/1.07      inference('sup-', [status(thm)], ['4', '5'])).
% 0.88/1.07  thf('7', plain,
% 0.88/1.07      (![X0 : $i, X1 : $i]:
% 0.88/1.07         (((X1) = (k1_xboole_0)) | (zip_tseitin_1 @ k1_xboole_0 @ X1 @ X0))),
% 0.88/1.07      inference('sup-', [status(thm)], ['3', '6'])).
% 0.88/1.07  thf(t61_funct_2, conjecture,
% 0.88/1.07    (![A:$i,B:$i,C:$i]:
% 0.88/1.07     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.88/1.07         ( m1_subset_1 @
% 0.88/1.07           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.88/1.07       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.88/1.07         ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ))).
% 0.88/1.07  thf(zf_stmt_5, negated_conjecture,
% 0.88/1.07    (~( ![A:$i,B:$i,C:$i]:
% 0.88/1.07        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.88/1.07            ( m1_subset_1 @
% 0.88/1.07              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.88/1.07          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.88/1.07            ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )),
% 0.88/1.07    inference('cnf.neg', [status(esa)], [t61_funct_2])).
% 0.88/1.07  thf('8', plain, ((v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B_2)),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.88/1.07  thf(t56_relat_1, axiom,
% 0.88/1.07    (![A:$i]:
% 0.88/1.07     ( ( v1_relat_1 @ A ) =>
% 0.88/1.07       ( ( ![B:$i,C:$i]: ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) =>
% 0.88/1.07         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.88/1.07  thf('9', plain,
% 0.88/1.07      (![X24 : $i]:
% 0.88/1.07         ((r2_hidden @ (k4_tarski @ (sk_B_1 @ X24) @ (sk_C @ X24)) @ X24)
% 0.88/1.07          | ((X24) = (k1_xboole_0))
% 0.88/1.07          | ~ (v1_relat_1 @ X24))),
% 0.88/1.07      inference('cnf', [status(esa)], [t56_relat_1])).
% 0.88/1.07  thf('10', plain,
% 0.88/1.07      ((m1_subset_1 @ sk_C_1 @ 
% 0.88/1.07        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.88/1.07  thf(l3_subset_1, axiom,
% 0.88/1.07    (![A:$i,B:$i]:
% 0.88/1.07     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.88/1.07       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.88/1.07  thf('11', plain,
% 0.88/1.07      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.88/1.07         (~ (r2_hidden @ X15 @ X16)
% 0.88/1.07          | (r2_hidden @ X15 @ X17)
% 0.88/1.07          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.88/1.07      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.88/1.07  thf('12', plain,
% 0.88/1.07      (![X0 : $i]:
% 0.88/1.07         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2))
% 0.88/1.07          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.88/1.07      inference('sup-', [status(thm)], ['10', '11'])).
% 0.88/1.07  thf('13', plain,
% 0.88/1.07      ((~ (v1_relat_1 @ sk_C_1)
% 0.88/1.07        | ((sk_C_1) = (k1_xboole_0))
% 0.88/1.07        | (r2_hidden @ (k4_tarski @ (sk_B_1 @ sk_C_1) @ (sk_C @ sk_C_1)) @ 
% 0.88/1.07           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.88/1.07      inference('sup-', [status(thm)], ['9', '12'])).
% 0.88/1.07  thf('14', plain,
% 0.88/1.07      ((m1_subset_1 @ sk_C_1 @ 
% 0.88/1.07        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.88/1.07  thf(cc1_relset_1, axiom,
% 0.88/1.07    (![A:$i,B:$i,C:$i]:
% 0.88/1.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.88/1.07       ( v1_relat_1 @ C ) ))).
% 0.88/1.07  thf('15', plain,
% 0.88/1.07      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.88/1.07         ((v1_relat_1 @ X33)
% 0.88/1.07          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.88/1.07      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.88/1.07  thf('16', plain, ((v1_relat_1 @ sk_C_1)),
% 0.88/1.07      inference('sup-', [status(thm)], ['14', '15'])).
% 0.88/1.07  thf('17', plain,
% 0.88/1.07      ((((sk_C_1) = (k1_xboole_0))
% 0.88/1.07        | (r2_hidden @ (k4_tarski @ (sk_B_1 @ sk_C_1) @ (sk_C @ sk_C_1)) @ 
% 0.88/1.07           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.88/1.07      inference('demod', [status(thm)], ['13', '16'])).
% 0.88/1.07  thf(t128_zfmisc_1, axiom,
% 0.88/1.07    (![A:$i,B:$i,C:$i,D:$i]:
% 0.88/1.07     ( ( r2_hidden @
% 0.88/1.07         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.88/1.07       ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ))).
% 0.88/1.07  thf('18', plain,
% 0.88/1.07      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.88/1.07         (((X10) = (X9))
% 0.88/1.07          | ~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ 
% 0.88/1.07               (k2_zfmisc_1 @ (k1_tarski @ X9) @ X12)))),
% 0.88/1.07      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 0.88/1.07  thf('19', plain,
% 0.88/1.07      ((((sk_C_1) = (k1_xboole_0)) | ((sk_B_1 @ sk_C_1) = (sk_A)))),
% 0.88/1.07      inference('sup-', [status(thm)], ['17', '18'])).
% 0.88/1.07  thf('20', plain,
% 0.88/1.07      (![X24 : $i]:
% 0.88/1.07         ((r2_hidden @ (k4_tarski @ (sk_B_1 @ X24) @ (sk_C @ X24)) @ X24)
% 0.88/1.07          | ((X24) = (k1_xboole_0))
% 0.88/1.07          | ~ (v1_relat_1 @ X24))),
% 0.88/1.07      inference('cnf', [status(esa)], [t56_relat_1])).
% 0.88/1.07  thf('21', plain,
% 0.88/1.07      (((r2_hidden @ (k4_tarski @ sk_A @ (sk_C @ sk_C_1)) @ sk_C_1)
% 0.88/1.07        | ((sk_C_1) = (k1_xboole_0))
% 0.88/1.07        | ~ (v1_relat_1 @ sk_C_1)
% 0.88/1.07        | ((sk_C_1) = (k1_xboole_0)))),
% 0.88/1.07      inference('sup+', [status(thm)], ['19', '20'])).
% 0.88/1.07  thf('22', plain, ((v1_relat_1 @ sk_C_1)),
% 0.88/1.07      inference('sup-', [status(thm)], ['14', '15'])).
% 0.88/1.07  thf('23', plain,
% 0.88/1.07      (((r2_hidden @ (k4_tarski @ sk_A @ (sk_C @ sk_C_1)) @ sk_C_1)
% 0.88/1.07        | ((sk_C_1) = (k1_xboole_0))
% 0.88/1.07        | ((sk_C_1) = (k1_xboole_0)))),
% 0.88/1.07      inference('demod', [status(thm)], ['21', '22'])).
% 0.88/1.07  thf('24', plain,
% 0.88/1.07      ((((sk_C_1) = (k1_xboole_0))
% 0.88/1.07        | (r2_hidden @ (k4_tarski @ sk_A @ (sk_C @ sk_C_1)) @ sk_C_1))),
% 0.88/1.07      inference('simplify', [status(thm)], ['23'])).
% 0.88/1.07  thf(t8_funct_1, axiom,
% 0.88/1.07    (![A:$i,B:$i,C:$i]:
% 0.88/1.07     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.88/1.07       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.88/1.07         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.88/1.07           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.88/1.07  thf('25', plain,
% 0.88/1.07      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.88/1.07         (~ (r2_hidden @ (k4_tarski @ X28 @ X30) @ X29)
% 0.88/1.07          | ((X30) = (k1_funct_1 @ X29 @ X28))
% 0.88/1.07          | ~ (v1_funct_1 @ X29)
% 0.88/1.07          | ~ (v1_relat_1 @ X29))),
% 0.88/1.07      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.88/1.07  thf('26', plain,
% 0.88/1.07      ((((sk_C_1) = (k1_xboole_0))
% 0.88/1.07        | ~ (v1_relat_1 @ sk_C_1)
% 0.88/1.07        | ~ (v1_funct_1 @ sk_C_1)
% 0.88/1.07        | ((sk_C @ sk_C_1) = (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.88/1.07      inference('sup-', [status(thm)], ['24', '25'])).
% 0.88/1.07  thf('27', plain, ((v1_relat_1 @ sk_C_1)),
% 0.88/1.07      inference('sup-', [status(thm)], ['14', '15'])).
% 0.88/1.07  thf('28', plain, ((v1_funct_1 @ sk_C_1)),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.88/1.07  thf('29', plain,
% 0.88/1.07      ((((sk_C_1) = (k1_xboole_0))
% 0.88/1.07        | ((sk_C @ sk_C_1) = (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.88/1.07      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.88/1.07  thf('30', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B_2)),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.88/1.07  thf('31', plain,
% 0.88/1.07      ((~ (r2_hidden @ (sk_C @ sk_C_1) @ sk_B_2) | ((sk_C_1) = (k1_xboole_0)))),
% 0.88/1.07      inference('sup-', [status(thm)], ['29', '30'])).
% 0.88/1.07  thf('32', plain,
% 0.88/1.07      ((((sk_C_1) = (k1_xboole_0))
% 0.88/1.07        | (r2_hidden @ (k4_tarski @ (sk_B_1 @ sk_C_1) @ (sk_C @ sk_C_1)) @ 
% 0.88/1.07           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.88/1.07      inference('demod', [status(thm)], ['13', '16'])).
% 0.88/1.07  thf('33', plain,
% 0.88/1.07      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.88/1.07         ((r2_hidden @ X11 @ X12)
% 0.88/1.07          | ~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ 
% 0.88/1.07               (k2_zfmisc_1 @ (k1_tarski @ X9) @ X12)))),
% 0.88/1.07      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 0.88/1.07  thf('34', plain,
% 0.88/1.07      ((((sk_C_1) = (k1_xboole_0)) | (r2_hidden @ (sk_C @ sk_C_1) @ sk_B_2))),
% 0.88/1.07      inference('sup-', [status(thm)], ['32', '33'])).
% 0.88/1.07  thf('35', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.88/1.07      inference('clc', [status(thm)], ['31', '34'])).
% 0.88/1.07  thf('36', plain, ((v1_funct_2 @ k1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_2)),
% 0.88/1.07      inference('demod', [status(thm)], ['8', '35'])).
% 0.88/1.07  thf('37', plain,
% 0.88/1.07      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.88/1.07         (~ (v1_funct_2 @ X48 @ X46 @ X47)
% 0.88/1.07          | ((X46) = (k1_relset_1 @ X46 @ X47 @ X48))
% 0.88/1.07          | ~ (zip_tseitin_1 @ X48 @ X47 @ X46))),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.88/1.07  thf('38', plain,
% 0.88/1.07      ((~ (zip_tseitin_1 @ k1_xboole_0 @ sk_B_2 @ (k1_tarski @ sk_A))
% 0.88/1.07        | ((k1_tarski @ sk_A)
% 0.88/1.07            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_2 @ k1_xboole_0)))),
% 0.88/1.07      inference('sup-', [status(thm)], ['36', '37'])).
% 0.88/1.07  thf('39', plain,
% 0.88/1.07      ((((sk_B_2) = (k1_xboole_0))
% 0.88/1.07        | ((k1_tarski @ sk_A)
% 0.88/1.07            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_2 @ k1_xboole_0)))),
% 0.88/1.07      inference('sup-', [status(thm)], ['7', '38'])).
% 0.88/1.07  thf('40', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.88/1.07      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.88/1.07  thf('41', plain,
% 0.88/1.07      (((k1_tarski @ sk_A)
% 0.88/1.07         = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_2 @ k1_xboole_0))),
% 0.88/1.07      inference('simplify_reflect-', [status(thm)], ['39', '40'])).
% 0.88/1.07  thf('42', plain,
% 0.88/1.07      (![X18 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X18))),
% 0.88/1.07      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.88/1.07  thf(t22_relset_1, axiom,
% 0.88/1.07    (![A:$i,B:$i,C:$i]:
% 0.88/1.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.88/1.07       ( ( ![D:$i]:
% 0.88/1.07           ( ~( ( r2_hidden @ D @ B ) & 
% 0.88/1.07                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 0.88/1.07         ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ))).
% 0.88/1.07  thf('43', plain,
% 0.88/1.07      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.88/1.07         (((k1_relset_1 @ X39 @ X40 @ X41) != (X39))
% 0.88/1.07          | ~ (r2_hidden @ X42 @ X39)
% 0.88/1.07          | (r2_hidden @ (k4_tarski @ X42 @ (sk_E @ X42 @ X41)) @ X41)
% 0.88/1.07          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40))))),
% 0.88/1.07      inference('cnf', [status(esa)], [t22_relset_1])).
% 0.88/1.07  thf('44', plain,
% 0.88/1.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.88/1.07         ((r2_hidden @ (k4_tarski @ X2 @ (sk_E @ X2 @ k1_xboole_0)) @ 
% 0.88/1.07           k1_xboole_0)
% 0.88/1.07          | ~ (r2_hidden @ X2 @ X1)
% 0.88/1.07          | ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) != (X1)))),
% 0.88/1.07      inference('sup-', [status(thm)], ['42', '43'])).
% 0.88/1.07  thf('45', plain,
% 0.88/1.07      (![X0 : $i]:
% 0.88/1.07         (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.88/1.07          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.88/1.07          | (r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ k1_xboole_0)) @ 
% 0.88/1.07             k1_xboole_0))),
% 0.88/1.07      inference('sup-', [status(thm)], ['41', '44'])).
% 0.88/1.07  thf('46', plain,
% 0.88/1.07      (![X0 : $i]:
% 0.88/1.07         ((r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ k1_xboole_0)) @ 
% 0.88/1.07           k1_xboole_0)
% 0.88/1.07          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.88/1.07      inference('simplify', [status(thm)], ['45'])).
% 0.88/1.07  thf('47', plain,
% 0.88/1.07      (((v1_xboole_0 @ (k1_tarski @ sk_A))
% 0.88/1.07        | (r2_hidden @ 
% 0.88/1.07           (k4_tarski @ (sk_B @ (k1_tarski @ sk_A)) @ 
% 0.88/1.07            (sk_E @ (sk_B @ (k1_tarski @ sk_A)) @ k1_xboole_0)) @ 
% 0.88/1.07           k1_xboole_0))),
% 0.88/1.07      inference('sup-', [status(thm)], ['2', '46'])).
% 0.88/1.07  thf(t69_enumset1, axiom,
% 0.88/1.07    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.88/1.07  thf('48', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.88/1.07      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.88/1.07  thf(fc3_xboole_0, axiom,
% 0.88/1.07    (![A:$i,B:$i]: ( ~( v1_xboole_0 @ ( k2_tarski @ A @ B ) ) ))).
% 0.88/1.07  thf('49', plain,
% 0.88/1.07      (![X7 : $i, X8 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X7 @ X8))),
% 0.88/1.07      inference('cnf', [status(esa)], [fc3_xboole_0])).
% 0.88/1.07  thf('50', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.88/1.07      inference('sup-', [status(thm)], ['48', '49'])).
% 0.88/1.07  thf('51', plain,
% 0.88/1.07      ((r2_hidden @ 
% 0.88/1.07        (k4_tarski @ (sk_B @ (k1_tarski @ sk_A)) @ 
% 0.88/1.07         (sk_E @ (sk_B @ (k1_tarski @ sk_A)) @ k1_xboole_0)) @ 
% 0.88/1.07        k1_xboole_0)),
% 0.88/1.07      inference('clc', [status(thm)], ['47', '50'])).
% 0.88/1.07  thf(t7_ordinal1, axiom,
% 0.88/1.07    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.88/1.07  thf('52', plain,
% 0.88/1.07      (![X31 : $i, X32 : $i]:
% 0.88/1.07         (~ (r2_hidden @ X31 @ X32) | ~ (r1_tarski @ X32 @ X31))),
% 0.88/1.07      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.88/1.07  thf('53', plain,
% 0.88/1.07      (~ (r1_tarski @ k1_xboole_0 @ 
% 0.88/1.07          (k4_tarski @ (sk_B @ (k1_tarski @ sk_A)) @ 
% 0.88/1.07           (sk_E @ (sk_B @ (k1_tarski @ sk_A)) @ k1_xboole_0)))),
% 0.88/1.07      inference('sup-', [status(thm)], ['51', '52'])).
% 0.88/1.07  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.88/1.07  thf('54', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.88/1.07      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.88/1.07  thf('55', plain, ($false), inference('demod', [status(thm)], ['53', '54'])).
% 0.88/1.07  
% 0.88/1.07  % SZS output end Refutation
% 0.88/1.07  
% 0.92/1.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
