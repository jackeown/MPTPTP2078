%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6eckdslsTC

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:19 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 364 expanded)
%              Number of leaves         :   51 ( 132 expanded)
%              Depth                    :   13
%              Number of atoms          :  843 (3791 expanded)
%              Number of equality atoms :   65 ( 204 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ ( sk_B @ X9 ) @ X9 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t61_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_funct_2])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t22_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) )
      <=> ( ( k1_relset_1 @ B @ A @ C )
          = B ) ) ) )).

thf('4',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( ( k1_relset_1 @ X36 @ X37 @ X38 )
       != X36 )
      | ~ ( r2_hidden @ X39 @ X36 )
      | ( r2_hidden @ ( k4_tarski @ X39 @ ( sk_E @ X39 @ X38 ) ) @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[t22_relset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_C ) ) @ sk_C )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
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

thf('7',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_funct_2 @ X45 @ X43 @ X44 )
      | ( X43
        = ( k1_relset_1 @ X43 @ X44 @ X45 ) )
      | ~ ( zip_tseitin_1 @ X45 @ X44 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('8',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X41: $i,X42: $i] :
      ( ( zip_tseitin_0 @ X41 @ X42 )
      | ( X41 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
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

thf('11',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( zip_tseitin_0 @ X46 @ X47 )
      | ( zip_tseitin_1 @ X48 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('12',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    zip_tseitin_1 @ sk_C @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C ) ),
    inference(demod,[status(thm)],['8','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_C ) ) @ sk_C )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['5','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_C ) ) @ sk_C ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ ( sk_E @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ sk_C ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['2','18'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('20',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(fc3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X7: $i,X8: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc3_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ ( sk_E @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ sk_C ) ) @ sk_C ),
    inference(clc,[status(thm)],['19','22'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('24',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X28 @ X29 )
      | ~ ( r1_tarski @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('25',plain,(
    ~ ( r1_tarski @ sk_C @ ( k4_tarski @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ ( sk_E @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('27',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v4_relat_1 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('28',plain,(
    v4_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X22: $i,X23: $i] :
      ( ( X22
        = ( k7_relat_1 @ X22 @ X23 ) )
      | ~ ( v4_relat_1 @ X22 @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('32',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v1_relat_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('33',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','33'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('35',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) )
        = ( k9_relat_1 @ X18 @ X19 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('36',plain,(
    ! [X24: $i] :
      ( ( ( k2_relat_1 @ X24 )
       != k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k9_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['31','32'])).

thf('40',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','33'])).

thf('41',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['31','32'])).

thf('42',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','33'])).

thf('43',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) )
        = ( k9_relat_1 @ X18 @ X19 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('44',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['31','32'])).

thf('46',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_C )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39','40','41','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v5_relat_1 @ X33 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('50',plain,(
    v5_relat_1 @ sk_C @ sk_B_1 ),
    inference('sup-',[status(thm)],['48','49'])).

thf(t205_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf('51',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k11_relat_1 @ X20 @ X21 )
        = k1_xboole_0 )
      | ( r2_hidden @ X21 @ ( k1_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf(t172_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) )).

thf('52',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X25 @ ( k1_relat_1 @ X26 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X26 @ X25 ) @ X27 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v5_relat_1 @ X26 @ X27 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t172_funct_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v5_relat_1 @ X0 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v5_relat_1 @ X0 @ X2 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( ( k11_relat_1 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['50','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['31','32'])).

thf('57',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k11_relat_1 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['58','59'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('61',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k11_relat_1 @ X16 @ X17 )
        = ( k9_relat_1 @ X16 @ ( k1_tarski @ X17 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('62',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('63',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k11_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['31','32'])).

thf('65',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k11_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['60','65'])).

thf('67',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','66'])).

thf('68',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['67'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('70',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('71',plain,(
    $false ),
    inference(demod,[status(thm)],['25','68','69','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6eckdslsTC
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:27:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.59/0.79  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.79  % Solved by: fo/fo7.sh
% 0.59/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.79  % done 478 iterations in 0.344s
% 0.59/0.79  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.79  % SZS output start Refutation
% 0.59/0.79  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.59/0.79  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.59/0.79  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.59/0.79  thf(sk_B_type, type, sk_B: $i > $i).
% 0.59/0.79  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.59/0.79  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.59/0.79  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.59/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.79  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.59/0.79  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.59/0.79  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.59/0.79  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.59/0.79  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.79  thf(sk_E_type, type, sk_E: $i > $i > $i).
% 0.59/0.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.79  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.59/0.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.79  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.59/0.79  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.59/0.79  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.79  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.59/0.79  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.59/0.79  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.59/0.79  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.59/0.79  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.59/0.79  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.59/0.79  thf(sk_C_type, type, sk_C: $i).
% 0.59/0.79  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.59/0.79  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.59/0.79  thf(existence_m1_subset_1, axiom,
% 0.59/0.79    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.59/0.79  thf('0', plain, (![X9 : $i]: (m1_subset_1 @ (sk_B @ X9) @ X9)),
% 0.59/0.79      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.59/0.79  thf(t2_subset, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( m1_subset_1 @ A @ B ) =>
% 0.59/0.79       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.59/0.79  thf('1', plain,
% 0.59/0.79      (![X11 : $i, X12 : $i]:
% 0.59/0.79         ((r2_hidden @ X11 @ X12)
% 0.59/0.79          | (v1_xboole_0 @ X12)
% 0.59/0.79          | ~ (m1_subset_1 @ X11 @ X12))),
% 0.59/0.79      inference('cnf', [status(esa)], [t2_subset])).
% 0.59/0.79  thf('2', plain,
% 0.59/0.79      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['0', '1'])).
% 0.59/0.79  thf(t61_funct_2, conjecture,
% 0.59/0.79    (![A:$i,B:$i,C:$i]:
% 0.59/0.79     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.59/0.79         ( m1_subset_1 @
% 0.59/0.79           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.59/0.79       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.59/0.79         ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ))).
% 0.59/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.79    (~( ![A:$i,B:$i,C:$i]:
% 0.59/0.79        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.59/0.79            ( m1_subset_1 @
% 0.59/0.79              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.59/0.79          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.59/0.79            ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )),
% 0.59/0.79    inference('cnf.neg', [status(esa)], [t61_funct_2])).
% 0.59/0.79  thf('3', plain,
% 0.59/0.79      ((m1_subset_1 @ sk_C @ 
% 0.59/0.79        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf(t22_relset_1, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i]:
% 0.59/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.59/0.79       ( ( ![D:$i]:
% 0.59/0.79           ( ~( ( r2_hidden @ D @ B ) & 
% 0.59/0.79                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 0.59/0.79         ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ))).
% 0.59/0.79  thf('4', plain,
% 0.59/0.79      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.59/0.79         (((k1_relset_1 @ X36 @ X37 @ X38) != (X36))
% 0.59/0.79          | ~ (r2_hidden @ X39 @ X36)
% 0.59/0.79          | (r2_hidden @ (k4_tarski @ X39 @ (sk_E @ X39 @ X38)) @ X38)
% 0.59/0.79          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 0.59/0.79      inference('cnf', [status(esa)], [t22_relset_1])).
% 0.59/0.79  thf('5', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         ((r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_C)) @ sk_C)
% 0.59/0.79          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.59/0.79          | ((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.59/0.79              != (k1_tarski @ sk_A)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['3', '4'])).
% 0.59/0.79  thf('6', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf(d1_funct_2, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i]:
% 0.59/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.79       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.59/0.79           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.59/0.79             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.59/0.79         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.59/0.79           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.59/0.79             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.59/0.79  thf(zf_stmt_1, axiom,
% 0.59/0.79    (![C:$i,B:$i,A:$i]:
% 0.59/0.79     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.59/0.79       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.59/0.79  thf('7', plain,
% 0.59/0.79      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.59/0.79         (~ (v1_funct_2 @ X45 @ X43 @ X44)
% 0.59/0.79          | ((X43) = (k1_relset_1 @ X43 @ X44 @ X45))
% 0.59/0.79          | ~ (zip_tseitin_1 @ X45 @ X44 @ X43))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.59/0.79  thf('8', plain,
% 0.59/0.79      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.59/0.79        | ((k1_tarski @ sk_A)
% 0.59/0.79            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['6', '7'])).
% 0.59/0.79  thf(zf_stmt_2, axiom,
% 0.59/0.79    (![B:$i,A:$i]:
% 0.59/0.79     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.59/0.79       ( zip_tseitin_0 @ B @ A ) ))).
% 0.59/0.79  thf('9', plain,
% 0.59/0.79      (![X41 : $i, X42 : $i]:
% 0.59/0.79         ((zip_tseitin_0 @ X41 @ X42) | ((X41) = (k1_xboole_0)))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.59/0.79  thf('10', plain,
% 0.59/0.79      ((m1_subset_1 @ sk_C @ 
% 0.59/0.79        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.59/0.79  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.59/0.79  thf(zf_stmt_5, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i]:
% 0.59/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.79       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.59/0.79         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.59/0.79           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.59/0.79             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.59/0.79  thf('11', plain,
% 0.59/0.79      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.59/0.79         (~ (zip_tseitin_0 @ X46 @ X47)
% 0.59/0.79          | (zip_tseitin_1 @ X48 @ X46 @ X47)
% 0.59/0.79          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46))))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.59/0.79  thf('12', plain,
% 0.59/0.79      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.59/0.79        | ~ (zip_tseitin_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['10', '11'])).
% 0.59/0.79  thf('13', plain,
% 0.59/0.79      ((((sk_B_1) = (k1_xboole_0))
% 0.59/0.79        | (zip_tseitin_1 @ sk_C @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['9', '12'])).
% 0.59/0.79  thf('14', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('15', plain, ((zip_tseitin_1 @ sk_C @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.59/0.79      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.59/0.79  thf('16', plain,
% 0.59/0.79      (((k1_tarski @ sk_A) = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C))),
% 0.59/0.79      inference('demod', [status(thm)], ['8', '15'])).
% 0.59/0.79  thf('17', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         ((r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_C)) @ sk_C)
% 0.59/0.79          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.59/0.79          | ((k1_tarski @ sk_A) != (k1_tarski @ sk_A)))),
% 0.59/0.79      inference('demod', [status(thm)], ['5', '16'])).
% 0.59/0.79  thf('18', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.59/0.79          | (r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_C)) @ sk_C))),
% 0.59/0.79      inference('simplify', [status(thm)], ['17'])).
% 0.59/0.79  thf('19', plain,
% 0.59/0.79      (((v1_xboole_0 @ (k1_tarski @ sk_A))
% 0.59/0.79        | (r2_hidden @ 
% 0.59/0.79           (k4_tarski @ (sk_B @ (k1_tarski @ sk_A)) @ 
% 0.59/0.79            (sk_E @ (sk_B @ (k1_tarski @ sk_A)) @ sk_C)) @ 
% 0.59/0.79           sk_C))),
% 0.59/0.79      inference('sup-', [status(thm)], ['2', '18'])).
% 0.59/0.79  thf(t69_enumset1, axiom,
% 0.59/0.79    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.59/0.79  thf('20', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.59/0.79      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.59/0.79  thf(fc3_xboole_0, axiom,
% 0.59/0.79    (![A:$i,B:$i]: ( ~( v1_xboole_0 @ ( k2_tarski @ A @ B ) ) ))).
% 0.59/0.79  thf('21', plain,
% 0.59/0.79      (![X7 : $i, X8 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X7 @ X8))),
% 0.59/0.79      inference('cnf', [status(esa)], [fc3_xboole_0])).
% 0.59/0.79  thf('22', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['20', '21'])).
% 0.59/0.79  thf('23', plain,
% 0.59/0.79      ((r2_hidden @ 
% 0.59/0.79        (k4_tarski @ (sk_B @ (k1_tarski @ sk_A)) @ 
% 0.59/0.79         (sk_E @ (sk_B @ (k1_tarski @ sk_A)) @ sk_C)) @ 
% 0.59/0.79        sk_C)),
% 0.59/0.79      inference('clc', [status(thm)], ['19', '22'])).
% 0.59/0.79  thf(t7_ordinal1, axiom,
% 0.59/0.79    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.59/0.79  thf('24', plain,
% 0.59/0.79      (![X28 : $i, X29 : $i]:
% 0.59/0.79         (~ (r2_hidden @ X28 @ X29) | ~ (r1_tarski @ X29 @ X28))),
% 0.59/0.79      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.59/0.79  thf('25', plain,
% 0.59/0.79      (~ (r1_tarski @ sk_C @ 
% 0.59/0.79          (k4_tarski @ (sk_B @ (k1_tarski @ sk_A)) @ 
% 0.59/0.79           (sk_E @ (sk_B @ (k1_tarski @ sk_A)) @ sk_C)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['23', '24'])).
% 0.59/0.79  thf('26', plain,
% 0.59/0.79      ((m1_subset_1 @ sk_C @ 
% 0.59/0.79        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf(cc2_relset_1, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i]:
% 0.59/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.79       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.59/0.79  thf('27', plain,
% 0.59/0.79      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.59/0.79         ((v4_relat_1 @ X33 @ X34)
% 0.59/0.79          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.59/0.79      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.59/0.79  thf('28', plain, ((v4_relat_1 @ sk_C @ (k1_tarski @ sk_A))),
% 0.59/0.79      inference('sup-', [status(thm)], ['26', '27'])).
% 0.59/0.79  thf(t209_relat_1, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.59/0.79       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.59/0.79  thf('29', plain,
% 0.59/0.79      (![X22 : $i, X23 : $i]:
% 0.59/0.79         (((X22) = (k7_relat_1 @ X22 @ X23))
% 0.59/0.79          | ~ (v4_relat_1 @ X22 @ X23)
% 0.59/0.79          | ~ (v1_relat_1 @ X22))),
% 0.59/0.79      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.59/0.79  thf('30', plain,
% 0.59/0.79      ((~ (v1_relat_1 @ sk_C)
% 0.59/0.79        | ((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A))))),
% 0.59/0.79      inference('sup-', [status(thm)], ['28', '29'])).
% 0.59/0.79  thf('31', plain,
% 0.59/0.79      ((m1_subset_1 @ sk_C @ 
% 0.59/0.79        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf(cc1_relset_1, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i]:
% 0.59/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.79       ( v1_relat_1 @ C ) ))).
% 0.59/0.79  thf('32', plain,
% 0.59/0.79      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.59/0.79         ((v1_relat_1 @ X30)
% 0.59/0.79          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.59/0.79      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.59/0.79  thf('33', plain, ((v1_relat_1 @ sk_C)),
% 0.59/0.79      inference('sup-', [status(thm)], ['31', '32'])).
% 0.59/0.79  thf('34', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.59/0.79      inference('demod', [status(thm)], ['30', '33'])).
% 0.59/0.79  thf(t148_relat_1, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( v1_relat_1 @ B ) =>
% 0.59/0.79       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.59/0.79  thf('35', plain,
% 0.59/0.79      (![X18 : $i, X19 : $i]:
% 0.59/0.79         (((k2_relat_1 @ (k7_relat_1 @ X18 @ X19)) = (k9_relat_1 @ X18 @ X19))
% 0.59/0.79          | ~ (v1_relat_1 @ X18))),
% 0.59/0.79      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.59/0.79  thf(t64_relat_1, axiom,
% 0.59/0.79    (![A:$i]:
% 0.59/0.79     ( ( v1_relat_1 @ A ) =>
% 0.59/0.79       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.59/0.79           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.59/0.79         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.59/0.79  thf('36', plain,
% 0.59/0.79      (![X24 : $i]:
% 0.59/0.79         (((k2_relat_1 @ X24) != (k1_xboole_0))
% 0.59/0.79          | ((X24) = (k1_xboole_0))
% 0.59/0.79          | ~ (v1_relat_1 @ X24))),
% 0.59/0.79      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.59/0.79  thf('37', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         (((k9_relat_1 @ X1 @ X0) != (k1_xboole_0))
% 0.59/0.79          | ~ (v1_relat_1 @ X1)
% 0.59/0.79          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.59/0.79          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['35', '36'])).
% 0.59/0.79  thf('38', plain,
% 0.59/0.79      ((~ (v1_relat_1 @ sk_C)
% 0.59/0.79        | ((k7_relat_1 @ sk_C @ (k1_tarski @ sk_A)) = (k1_xboole_0))
% 0.59/0.79        | ~ (v1_relat_1 @ sk_C)
% 0.59/0.79        | ((k9_relat_1 @ sk_C @ (k1_tarski @ sk_A)) != (k1_xboole_0)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['34', '37'])).
% 0.59/0.79  thf('39', plain, ((v1_relat_1 @ sk_C)),
% 0.59/0.79      inference('sup-', [status(thm)], ['31', '32'])).
% 0.59/0.79  thf('40', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.59/0.79      inference('demod', [status(thm)], ['30', '33'])).
% 0.59/0.79  thf('41', plain, ((v1_relat_1 @ sk_C)),
% 0.59/0.79      inference('sup-', [status(thm)], ['31', '32'])).
% 0.59/0.79  thf('42', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.59/0.79      inference('demod', [status(thm)], ['30', '33'])).
% 0.59/0.79  thf('43', plain,
% 0.59/0.79      (![X18 : $i, X19 : $i]:
% 0.59/0.79         (((k2_relat_1 @ (k7_relat_1 @ X18 @ X19)) = (k9_relat_1 @ X18 @ X19))
% 0.59/0.79          | ~ (v1_relat_1 @ X18))),
% 0.59/0.79      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.59/0.79  thf('44', plain,
% 0.59/0.79      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_tarski @ sk_A)))
% 0.59/0.79        | ~ (v1_relat_1 @ sk_C))),
% 0.59/0.79      inference('sup+', [status(thm)], ['42', '43'])).
% 0.59/0.79  thf('45', plain, ((v1_relat_1 @ sk_C)),
% 0.59/0.79      inference('sup-', [status(thm)], ['31', '32'])).
% 0.59/0.79  thf('46', plain,
% 0.59/0.79      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.59/0.79      inference('demod', [status(thm)], ['44', '45'])).
% 0.59/0.79  thf('47', plain,
% 0.59/0.79      ((((sk_C) = (k1_xboole_0)) | ((k2_relat_1 @ sk_C) != (k1_xboole_0)))),
% 0.59/0.79      inference('demod', [status(thm)], ['38', '39', '40', '41', '46'])).
% 0.59/0.79  thf('48', plain,
% 0.59/0.79      ((m1_subset_1 @ sk_C @ 
% 0.59/0.79        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('49', plain,
% 0.59/0.79      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.59/0.79         ((v5_relat_1 @ X33 @ X35)
% 0.59/0.79          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.59/0.79      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.59/0.79  thf('50', plain, ((v5_relat_1 @ sk_C @ sk_B_1)),
% 0.59/0.79      inference('sup-', [status(thm)], ['48', '49'])).
% 0.59/0.79  thf(t205_relat_1, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( v1_relat_1 @ B ) =>
% 0.59/0.79       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.59/0.79         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.59/0.79  thf('51', plain,
% 0.59/0.79      (![X20 : $i, X21 : $i]:
% 0.59/0.79         (((k11_relat_1 @ X20 @ X21) = (k1_xboole_0))
% 0.59/0.79          | (r2_hidden @ X21 @ (k1_relat_1 @ X20))
% 0.59/0.79          | ~ (v1_relat_1 @ X20))),
% 0.59/0.79      inference('cnf', [status(esa)], [t205_relat_1])).
% 0.59/0.79  thf(t172_funct_1, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.59/0.79       ( ![C:$i]:
% 0.59/0.79         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.59/0.79           ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) ))).
% 0.59/0.79  thf('52', plain,
% 0.59/0.79      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.59/0.79         (~ (r2_hidden @ X25 @ (k1_relat_1 @ X26))
% 0.59/0.79          | (r2_hidden @ (k1_funct_1 @ X26 @ X25) @ X27)
% 0.59/0.79          | ~ (v1_funct_1 @ X26)
% 0.59/0.79          | ~ (v5_relat_1 @ X26 @ X27)
% 0.59/0.79          | ~ (v1_relat_1 @ X26))),
% 0.59/0.79      inference('cnf', [status(esa)], [t172_funct_1])).
% 0.59/0.79  thf('53', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.79         (~ (v1_relat_1 @ X0)
% 0.59/0.79          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.59/0.79          | ~ (v1_relat_1 @ X0)
% 0.59/0.79          | ~ (v5_relat_1 @ X0 @ X2)
% 0.59/0.79          | ~ (v1_funct_1 @ X0)
% 0.59/0.79          | (r2_hidden @ (k1_funct_1 @ X0 @ X1) @ X2))),
% 0.59/0.79      inference('sup-', [status(thm)], ['51', '52'])).
% 0.59/0.79  thf('54', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.79         ((r2_hidden @ (k1_funct_1 @ X0 @ X1) @ X2)
% 0.59/0.79          | ~ (v1_funct_1 @ X0)
% 0.59/0.79          | ~ (v5_relat_1 @ X0 @ X2)
% 0.59/0.79          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.59/0.79          | ~ (v1_relat_1 @ X0))),
% 0.59/0.79      inference('simplify', [status(thm)], ['53'])).
% 0.59/0.79  thf('55', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (v1_relat_1 @ sk_C)
% 0.59/0.79          | ((k11_relat_1 @ sk_C @ X0) = (k1_xboole_0))
% 0.59/0.79          | ~ (v1_funct_1 @ sk_C)
% 0.59/0.79          | (r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_1))),
% 0.59/0.79      inference('sup-', [status(thm)], ['50', '54'])).
% 0.59/0.79  thf('56', plain, ((v1_relat_1 @ sk_C)),
% 0.59/0.79      inference('sup-', [status(thm)], ['31', '32'])).
% 0.59/0.79  thf('57', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('58', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (((k11_relat_1 @ sk_C @ X0) = (k1_xboole_0))
% 0.59/0.79          | (r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_1))),
% 0.59/0.79      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.59/0.79  thf('59', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_1)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('60', plain, (((k11_relat_1 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['58', '59'])).
% 0.59/0.79  thf(d16_relat_1, axiom,
% 0.59/0.79    (![A:$i]:
% 0.59/0.79     ( ( v1_relat_1 @ A ) =>
% 0.59/0.79       ( ![B:$i]:
% 0.59/0.79         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.59/0.79  thf('61', plain,
% 0.59/0.79      (![X16 : $i, X17 : $i]:
% 0.59/0.79         (((k11_relat_1 @ X16 @ X17) = (k9_relat_1 @ X16 @ (k1_tarski @ X17)))
% 0.59/0.79          | ~ (v1_relat_1 @ X16))),
% 0.59/0.79      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.59/0.79  thf('62', plain,
% 0.59/0.79      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.59/0.79      inference('demod', [status(thm)], ['44', '45'])).
% 0.59/0.79  thf('63', plain,
% 0.59/0.79      ((((k2_relat_1 @ sk_C) = (k11_relat_1 @ sk_C @ sk_A))
% 0.59/0.79        | ~ (v1_relat_1 @ sk_C))),
% 0.59/0.79      inference('sup+', [status(thm)], ['61', '62'])).
% 0.59/0.79  thf('64', plain, ((v1_relat_1 @ sk_C)),
% 0.59/0.79      inference('sup-', [status(thm)], ['31', '32'])).
% 0.59/0.79  thf('65', plain, (((k2_relat_1 @ sk_C) = (k11_relat_1 @ sk_C @ sk_A))),
% 0.59/0.79      inference('demod', [status(thm)], ['63', '64'])).
% 0.59/0.79  thf('66', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.59/0.79      inference('sup+', [status(thm)], ['60', '65'])).
% 0.59/0.79  thf('67', plain,
% 0.59/0.79      ((((sk_C) = (k1_xboole_0)) | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.59/0.79      inference('demod', [status(thm)], ['47', '66'])).
% 0.59/0.79  thf('68', plain, (((sk_C) = (k1_xboole_0))),
% 0.59/0.79      inference('simplify', [status(thm)], ['67'])).
% 0.59/0.79  thf('69', plain, (((sk_C) = (k1_xboole_0))),
% 0.59/0.79      inference('simplify', [status(thm)], ['67'])).
% 0.59/0.79  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.59/0.79  thf('70', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.59/0.79      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.59/0.79  thf('71', plain, ($false),
% 0.59/0.79      inference('demod', [status(thm)], ['25', '68', '69', '70'])).
% 0.59/0.79  
% 0.59/0.79  % SZS output end Refutation
% 0.59/0.79  
% 0.59/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
