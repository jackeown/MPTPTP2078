%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8oQi01CZwX

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:16 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 222 expanded)
%              Number of leaves         :   37 (  80 expanded)
%              Depth                    :   15
%              Number of atoms          :  831 (2445 expanded)
%              Number of equality atoms :   83 ( 217 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t11_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t11_funct_2])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_C @ ( k1_funct_2 @ sk_A @ sk_B ) ) ),
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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 = X0 )
      | ( zip_tseitin_0 @ X0 @ X3 )
      | ( zip_tseitin_0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('6',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_0 @ X17 @ X18 )
      | ( zip_tseitin_1 @ X19 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('7',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( sk_B = X1 )
      | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_0 @ X0 @ X1 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,
    ( ! [X1: $i] :
        ( ( zip_tseitin_0 @ k1_xboole_0 @ X1 )
        | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_2 @ X16 @ X14 @ X15 )
      | ( X14
        = ( k1_relset_1 @ X14 @ X15 @ X16 ) )
      | ~ ( zip_tseitin_1 @ X16 @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('15',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('17',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('18',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ k1_xboole_0 @ X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( zip_tseitin_0 @ X0 @ X1 )
        | ( zip_tseitin_0 @ X0 @ X2 )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','20'])).

thf('22',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( sk_A
          = ( k1_relat_1 @ sk_C ) )
        | ( zip_tseitin_0 @ X1 @ X0 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['21'])).

thf('23',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('24',plain,
    ( ( ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('26',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('28',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v5_relat_1 @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('29',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['27','28'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v5_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k2_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('35',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('36',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['31','36'])).

thf(d2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k1_funct_2 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i] :
              ( ( v1_relat_1 @ E )
              & ( v1_funct_1 @ E )
              & ( D = E )
              & ( ( k1_relat_1 @ E )
                = A )
              & ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) ) ) ) )).

thf(zf_stmt_6,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ E @ D @ B @ A )
    <=> ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B )
        & ( ( k1_relat_1 @ E )
          = A )
        & ( D = E )
        & ( v1_funct_1 @ E )
        & ( v1_relat_1 @ E ) ) ) )).

thf('38',plain,(
    ! [X20: $i,X21: $i,X22: $i,X24: $i] :
      ( ( zip_tseitin_2 @ X20 @ X22 @ X21 @ X24 )
      | ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ( X22 != X20 )
      | ( ( k1_relat_1 @ X20 )
       != X24 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('39',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X20 ) @ X21 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 )
      | ( zip_tseitin_2 @ X20 @ X20 @ X21 @ ( k1_relat_1 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( zip_tseitin_2 @ sk_C @ sk_C @ sk_B @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['34','35'])).

thf('42',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    zip_tseitin_2 @ sk_C @ sk_C @ sk_B @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ( zip_tseitin_2 @ sk_C @ sk_C @ sk_B @ sk_A )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','43'])).

thf(zf_stmt_7,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k1_funct_2 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i] :
              ( zip_tseitin_2 @ E @ D @ B @ A ) ) ) )).

thf('45',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_2 @ X25 @ X26 @ X27 @ X28 )
      | ( r2_hidden @ X26 @ X29 )
      | ( X29
       != ( k1_funct_2 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('46',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( r2_hidden @ X26 @ ( k1_funct_2 @ X28 @ X27 ) )
      | ~ ( zip_tseitin_2 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( r2_hidden @ sk_C @ ( k1_funct_2 @ sk_A @ sk_B ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('49',plain,(
    ~ ( r2_hidden @ sk_C @ ( k1_funct_2 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ~ ( r2_hidden @ sk_C @ ( k1_funct_2 @ k1_xboole_0 @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('52',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v1_funct_2 @ sk_C @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_2 @ X16 @ X14 @ X15 )
      | ( X14
        = ( k1_relset_1 @ X14 @ X15 @ X16 ) )
      | ~ ( zip_tseitin_1 @ X16 @ X15 @ X14 ) ) ),
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
    inference(split,[status(esa)],['9'])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_0 @ X17 @ X18 )
      | ( zip_tseitin_1 @ X19 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('60',plain,
    ( ( ( zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 )
      | ( X13 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('62',plain,(
    ! [X12: $i] :
      ( zip_tseitin_0 @ X12 @ k1_xboole_0 ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
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

thf('68',plain,(
    zip_tseitin_2 @ sk_C @ sk_C @ sk_B @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('69',plain,
    ( ( zip_tseitin_2 @ sk_C @ sk_C @ sk_B @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( r2_hidden @ X26 @ ( k1_funct_2 @ X28 @ X27 ) )
      | ~ ( zip_tseitin_2 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('71',plain,
    ( ( r2_hidden @ sk_C @ ( k1_funct_2 @ k1_xboole_0 @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['50','71'])).

thf('73',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('74',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['72','73'])).

thf('75',plain,(
    r2_hidden @ sk_C @ ( k1_funct_2 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['47','74'])).

thf('76',plain,(
    $false ),
    inference(demod,[status(thm)],['0','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8oQi01CZwX
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:23:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.44/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.66  % Solved by: fo/fo7.sh
% 0.44/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.66  % done 193 iterations in 0.199s
% 0.44/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.66  % SZS output start Refutation
% 0.44/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.66  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.44/0.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.44/0.66  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.44/0.66  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 0.44/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.66  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.44/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.44/0.66  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.44/0.66  thf(sk_C_type, type, sk_C: $i).
% 0.44/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.66  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $i > $o).
% 0.44/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.66  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.44/0.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.44/0.66  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.44/0.66  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.44/0.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.44/0.66  thf(t11_funct_2, conjecture,
% 0.44/0.66    (![A:$i,B:$i,C:$i]:
% 0.44/0.66     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.44/0.66         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.66       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.44/0.66         ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) ) ))).
% 0.44/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.66    (~( ![A:$i,B:$i,C:$i]:
% 0.44/0.66        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.44/0.66            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.66          ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.44/0.66            ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) ) ) )),
% 0.44/0.66    inference('cnf.neg', [status(esa)], [t11_funct_2])).
% 0.44/0.66  thf('0', plain, (~ (r2_hidden @ sk_C @ (k1_funct_2 @ sk_A @ sk_B))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf(d1_funct_2, axiom,
% 0.44/0.66    (![A:$i,B:$i,C:$i]:
% 0.44/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.66       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.44/0.66           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.44/0.66             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.44/0.66         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.44/0.66           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.44/0.66             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.44/0.66  thf(zf_stmt_1, axiom,
% 0.44/0.66    (![B:$i,A:$i]:
% 0.44/0.66     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.44/0.66       ( zip_tseitin_0 @ B @ A ) ))).
% 0.44/0.66  thf('1', plain,
% 0.44/0.66      (![X12 : $i, X13 : $i]:
% 0.44/0.66         ((zip_tseitin_0 @ X12 @ X13) | ((X12) = (k1_xboole_0)))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.66  thf('2', plain,
% 0.44/0.66      (![X12 : $i, X13 : $i]:
% 0.44/0.66         ((zip_tseitin_0 @ X12 @ X13) | ((X12) = (k1_xboole_0)))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.66  thf('3', plain,
% 0.44/0.66      (![X12 : $i, X13 : $i]:
% 0.44/0.66         ((zip_tseitin_0 @ X12 @ X13) | ((X12) = (k1_xboole_0)))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.66  thf('4', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.44/0.66         (((X1) = (X0)) | (zip_tseitin_0 @ X0 @ X3) | (zip_tseitin_0 @ X1 @ X2))),
% 0.44/0.66      inference('sup+', [status(thm)], ['2', '3'])).
% 0.44/0.66  thf('5', plain,
% 0.44/0.66      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.44/0.66  thf(zf_stmt_3, axiom,
% 0.44/0.66    (![C:$i,B:$i,A:$i]:
% 0.44/0.66     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.44/0.66       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.44/0.66  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.44/0.66  thf(zf_stmt_5, axiom,
% 0.44/0.66    (![A:$i,B:$i,C:$i]:
% 0.44/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.66       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.44/0.66         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.44/0.66           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.44/0.66             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.44/0.66  thf('6', plain,
% 0.44/0.66      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.44/0.66         (~ (zip_tseitin_0 @ X17 @ X18)
% 0.44/0.66          | (zip_tseitin_1 @ X19 @ X17 @ X18)
% 0.44/0.66          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X17))))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.44/0.66  thf('7', plain,
% 0.44/0.66      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.44/0.66      inference('sup-', [status(thm)], ['5', '6'])).
% 0.44/0.66  thf('8', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         ((zip_tseitin_0 @ X1 @ X0)
% 0.44/0.66          | ((sk_B) = (X1))
% 0.44/0.66          | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.44/0.66      inference('sup-', [status(thm)], ['4', '7'])).
% 0.44/0.66  thf('9', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B) != (k1_xboole_0)))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('10', plain,
% 0.44/0.66      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.44/0.66      inference('split', [status(esa)], ['9'])).
% 0.44/0.66  thf('11', plain,
% 0.44/0.66      ((![X0 : $i, X1 : $i]:
% 0.44/0.66          (((X0) != (k1_xboole_0))
% 0.44/0.66           | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.44/0.66           | (zip_tseitin_0 @ X0 @ X1)))
% 0.44/0.66         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.44/0.66      inference('sup-', [status(thm)], ['8', '10'])).
% 0.44/0.66  thf('12', plain,
% 0.44/0.66      ((![X1 : $i]:
% 0.44/0.66          ((zip_tseitin_0 @ k1_xboole_0 @ X1)
% 0.44/0.66           | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)))
% 0.44/0.66         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.44/0.66      inference('simplify', [status(thm)], ['11'])).
% 0.44/0.66  thf('13', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('14', plain,
% 0.44/0.66      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.44/0.66         (~ (v1_funct_2 @ X16 @ X14 @ X15)
% 0.44/0.66          | ((X14) = (k1_relset_1 @ X14 @ X15 @ X16))
% 0.44/0.66          | ~ (zip_tseitin_1 @ X16 @ X15 @ X14))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.44/0.66  thf('15', plain,
% 0.44/0.66      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.44/0.66        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.44/0.66      inference('sup-', [status(thm)], ['13', '14'])).
% 0.44/0.66  thf('16', plain,
% 0.44/0.66      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf(redefinition_k1_relset_1, axiom,
% 0.44/0.66    (![A:$i,B:$i,C:$i]:
% 0.44/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.66       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.44/0.66  thf('17', plain,
% 0.44/0.66      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.44/0.66         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.44/0.66          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.44/0.66      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.44/0.66  thf('18', plain,
% 0.44/0.66      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.44/0.66      inference('sup-', [status(thm)], ['16', '17'])).
% 0.44/0.66  thf('19', plain,
% 0.44/0.66      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.44/0.66      inference('demod', [status(thm)], ['15', '18'])).
% 0.44/0.66  thf('20', plain,
% 0.44/0.66      ((![X0 : $i]:
% 0.44/0.66          ((zip_tseitin_0 @ k1_xboole_0 @ X0) | ((sk_A) = (k1_relat_1 @ sk_C))))
% 0.44/0.66         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.44/0.66      inference('sup-', [status(thm)], ['12', '19'])).
% 0.44/0.66  thf('21', plain,
% 0.44/0.66      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.66          ((zip_tseitin_0 @ X0 @ X1)
% 0.44/0.66           | (zip_tseitin_0 @ X0 @ X2)
% 0.44/0.66           | ((sk_A) = (k1_relat_1 @ sk_C))))
% 0.44/0.66         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.44/0.66      inference('sup+', [status(thm)], ['1', '20'])).
% 0.44/0.66  thf('22', plain,
% 0.44/0.66      ((![X0 : $i, X1 : $i]:
% 0.44/0.66          (((sk_A) = (k1_relat_1 @ sk_C)) | (zip_tseitin_0 @ X1 @ X0)))
% 0.44/0.66         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.44/0.66      inference('condensation', [status(thm)], ['21'])).
% 0.44/0.66  thf('23', plain,
% 0.44/0.66      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.44/0.66      inference('sup-', [status(thm)], ['5', '6'])).
% 0.44/0.66  thf('24', plain,
% 0.44/0.66      (((((sk_A) = (k1_relat_1 @ sk_C)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)))
% 0.44/0.66         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.44/0.66      inference('sup-', [status(thm)], ['22', '23'])).
% 0.44/0.66  thf('25', plain,
% 0.44/0.66      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.44/0.66      inference('demod', [status(thm)], ['15', '18'])).
% 0.44/0.66  thf('26', plain,
% 0.44/0.66      ((((sk_A) = (k1_relat_1 @ sk_C))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.44/0.66      inference('clc', [status(thm)], ['24', '25'])).
% 0.44/0.66  thf('27', plain,
% 0.44/0.66      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf(cc2_relset_1, axiom,
% 0.44/0.66    (![A:$i,B:$i,C:$i]:
% 0.44/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.66       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.44/0.66  thf('28', plain,
% 0.44/0.66      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.44/0.66         ((v5_relat_1 @ X6 @ X8)
% 0.44/0.66          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.44/0.66      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.44/0.66  thf('29', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 0.44/0.66      inference('sup-', [status(thm)], ['27', '28'])).
% 0.44/0.66  thf(d19_relat_1, axiom,
% 0.44/0.66    (![A:$i,B:$i]:
% 0.44/0.66     ( ( v1_relat_1 @ B ) =>
% 0.44/0.66       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.44/0.66  thf('30', plain,
% 0.44/0.66      (![X2 : $i, X3 : $i]:
% 0.44/0.66         (~ (v5_relat_1 @ X2 @ X3)
% 0.44/0.66          | (r1_tarski @ (k2_relat_1 @ X2) @ X3)
% 0.44/0.66          | ~ (v1_relat_1 @ X2))),
% 0.44/0.66      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.44/0.66  thf('31', plain,
% 0.44/0.66      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 0.44/0.66      inference('sup-', [status(thm)], ['29', '30'])).
% 0.44/0.66  thf('32', plain,
% 0.44/0.66      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf(cc2_relat_1, axiom,
% 0.44/0.66    (![A:$i]:
% 0.44/0.66     ( ( v1_relat_1 @ A ) =>
% 0.44/0.66       ( ![B:$i]:
% 0.44/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.44/0.66  thf('33', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.44/0.66          | (v1_relat_1 @ X0)
% 0.44/0.66          | ~ (v1_relat_1 @ X1))),
% 0.44/0.66      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.44/0.66  thf('34', plain,
% 0.44/0.66      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.44/0.66      inference('sup-', [status(thm)], ['32', '33'])).
% 0.44/0.66  thf(fc6_relat_1, axiom,
% 0.44/0.66    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.44/0.66  thf('35', plain,
% 0.44/0.66      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.44/0.66      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.44/0.66  thf('36', plain, ((v1_relat_1 @ sk_C)),
% 0.44/0.66      inference('demod', [status(thm)], ['34', '35'])).
% 0.44/0.66  thf('37', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.44/0.66      inference('demod', [status(thm)], ['31', '36'])).
% 0.44/0.66  thf(d2_funct_2, axiom,
% 0.44/0.66    (![A:$i,B:$i,C:$i]:
% 0.44/0.66     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 0.44/0.66       ( ![D:$i]:
% 0.44/0.66         ( ( r2_hidden @ D @ C ) <=>
% 0.44/0.66           ( ?[E:$i]:
% 0.44/0.66             ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) & ( ( D ) = ( E ) ) & 
% 0.44/0.66               ( ( k1_relat_1 @ E ) = ( A ) ) & 
% 0.44/0.66               ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) ) ) ) ) ))).
% 0.44/0.66  thf(zf_stmt_6, axiom,
% 0.44/0.66    (![E:$i,D:$i,B:$i,A:$i]:
% 0.44/0.66     ( ( zip_tseitin_2 @ E @ D @ B @ A ) <=>
% 0.44/0.66       ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) & 
% 0.44/0.66         ( ( k1_relat_1 @ E ) = ( A ) ) & ( ( D ) = ( E ) ) & 
% 0.44/0.66         ( v1_funct_1 @ E ) & ( v1_relat_1 @ E ) ) ))).
% 0.44/0.66  thf('38', plain,
% 0.44/0.66      (![X20 : $i, X21 : $i, X22 : $i, X24 : $i]:
% 0.44/0.66         ((zip_tseitin_2 @ X20 @ X22 @ X21 @ X24)
% 0.44/0.66          | ~ (v1_relat_1 @ X20)
% 0.44/0.66          | ~ (v1_funct_1 @ X20)
% 0.44/0.66          | ((X22) != (X20))
% 0.44/0.66          | ((k1_relat_1 @ X20) != (X24))
% 0.44/0.66          | ~ (r1_tarski @ (k2_relat_1 @ X20) @ X21))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.44/0.66  thf('39', plain,
% 0.44/0.66      (![X20 : $i, X21 : $i]:
% 0.44/0.66         (~ (r1_tarski @ (k2_relat_1 @ X20) @ X21)
% 0.44/0.66          | ~ (v1_funct_1 @ X20)
% 0.44/0.66          | ~ (v1_relat_1 @ X20)
% 0.44/0.66          | (zip_tseitin_2 @ X20 @ X20 @ X21 @ (k1_relat_1 @ X20)))),
% 0.44/0.66      inference('simplify', [status(thm)], ['38'])).
% 0.44/0.66  thf('40', plain,
% 0.44/0.66      (((zip_tseitin_2 @ sk_C @ sk_C @ sk_B @ (k1_relat_1 @ sk_C))
% 0.44/0.66        | ~ (v1_relat_1 @ sk_C)
% 0.44/0.66        | ~ (v1_funct_1 @ sk_C))),
% 0.44/0.66      inference('sup-', [status(thm)], ['37', '39'])).
% 0.44/0.66  thf('41', plain, ((v1_relat_1 @ sk_C)),
% 0.44/0.66      inference('demod', [status(thm)], ['34', '35'])).
% 0.44/0.66  thf('42', plain, ((v1_funct_1 @ sk_C)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('43', plain,
% 0.44/0.66      ((zip_tseitin_2 @ sk_C @ sk_C @ sk_B @ (k1_relat_1 @ sk_C))),
% 0.44/0.66      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.44/0.66  thf('44', plain,
% 0.44/0.66      (((zip_tseitin_2 @ sk_C @ sk_C @ sk_B @ sk_A))
% 0.44/0.66         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.44/0.66      inference('sup+', [status(thm)], ['26', '43'])).
% 0.44/0.66  thf(zf_stmt_7, type, zip_tseitin_2 : $i > $i > $i > $i > $o).
% 0.44/0.66  thf(zf_stmt_8, axiom,
% 0.44/0.66    (![A:$i,B:$i,C:$i]:
% 0.44/0.66     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 0.44/0.66       ( ![D:$i]:
% 0.44/0.66         ( ( r2_hidden @ D @ C ) <=>
% 0.44/0.66           ( ?[E:$i]: ( zip_tseitin_2 @ E @ D @ B @ A ) ) ) ) ))).
% 0.44/0.66  thf('45', plain,
% 0.44/0.66      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.44/0.66         (~ (zip_tseitin_2 @ X25 @ X26 @ X27 @ X28)
% 0.44/0.66          | (r2_hidden @ X26 @ X29)
% 0.44/0.66          | ((X29) != (k1_funct_2 @ X28 @ X27)))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.44/0.66  thf('46', plain,
% 0.44/0.66      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.44/0.66         ((r2_hidden @ X26 @ (k1_funct_2 @ X28 @ X27))
% 0.44/0.66          | ~ (zip_tseitin_2 @ X25 @ X26 @ X27 @ X28))),
% 0.44/0.66      inference('simplify', [status(thm)], ['45'])).
% 0.44/0.66  thf('47', plain,
% 0.44/0.66      (((r2_hidden @ sk_C @ (k1_funct_2 @ sk_A @ sk_B)))
% 0.44/0.66         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.44/0.66      inference('sup-', [status(thm)], ['44', '46'])).
% 0.44/0.66  thf('48', plain,
% 0.44/0.66      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.66      inference('split', [status(esa)], ['9'])).
% 0.44/0.66  thf('49', plain, (~ (r2_hidden @ sk_C @ (k1_funct_2 @ sk_A @ sk_B))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('50', plain,
% 0.44/0.66      ((~ (r2_hidden @ sk_C @ (k1_funct_2 @ k1_xboole_0 @ sk_B)))
% 0.44/0.66         <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.66      inference('sup-', [status(thm)], ['48', '49'])).
% 0.44/0.66  thf('51', plain,
% 0.44/0.66      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.66      inference('split', [status(esa)], ['9'])).
% 0.44/0.66  thf('52', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('53', plain,
% 0.44/0.66      (((v1_funct_2 @ sk_C @ k1_xboole_0 @ sk_B))
% 0.44/0.66         <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.66      inference('sup+', [status(thm)], ['51', '52'])).
% 0.44/0.66  thf('54', plain,
% 0.44/0.66      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.44/0.66         (~ (v1_funct_2 @ X16 @ X14 @ X15)
% 0.44/0.66          | ((X14) = (k1_relset_1 @ X14 @ X15 @ X16))
% 0.44/0.66          | ~ (zip_tseitin_1 @ X16 @ X15 @ X14))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.44/0.66  thf('55', plain,
% 0.44/0.66      (((~ (zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0)
% 0.44/0.66         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C))))
% 0.44/0.66         <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.66      inference('sup-', [status(thm)], ['53', '54'])).
% 0.44/0.66  thf('56', plain,
% 0.44/0.66      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.66      inference('split', [status(esa)], ['9'])).
% 0.44/0.66  thf('57', plain,
% 0.44/0.66      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('58', plain,
% 0.44/0.66      (((m1_subset_1 @ sk_C @ 
% 0.44/0.66         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.44/0.66         <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.66      inference('sup+', [status(thm)], ['56', '57'])).
% 0.44/0.66  thf('59', plain,
% 0.44/0.66      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.44/0.66         (~ (zip_tseitin_0 @ X17 @ X18)
% 0.44/0.66          | (zip_tseitin_1 @ X19 @ X17 @ X18)
% 0.44/0.66          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X17))))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.44/0.66  thf('60', plain,
% 0.44/0.66      ((((zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0)
% 0.44/0.66         | ~ (zip_tseitin_0 @ sk_B @ k1_xboole_0)))
% 0.44/0.66         <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.66      inference('sup-', [status(thm)], ['58', '59'])).
% 0.44/0.66  thf('61', plain,
% 0.44/0.66      (![X12 : $i, X13 : $i]:
% 0.44/0.66         ((zip_tseitin_0 @ X12 @ X13) | ((X13) != (k1_xboole_0)))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.66  thf('62', plain, (![X12 : $i]: (zip_tseitin_0 @ X12 @ k1_xboole_0)),
% 0.44/0.66      inference('simplify', [status(thm)], ['61'])).
% 0.44/0.66  thf('63', plain,
% 0.44/0.66      (((zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0))
% 0.44/0.66         <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.66      inference('demod', [status(thm)], ['60', '62'])).
% 0.44/0.66  thf('64', plain,
% 0.44/0.66      (((m1_subset_1 @ sk_C @ 
% 0.44/0.66         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.44/0.66         <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.66      inference('sup+', [status(thm)], ['56', '57'])).
% 0.44/0.66  thf('65', plain,
% 0.44/0.66      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.44/0.66         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.44/0.66          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.44/0.66      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.44/0.66  thf('66', plain,
% 0.44/0.66      ((((k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C) = (k1_relat_1 @ sk_C)))
% 0.44/0.66         <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.66      inference('sup-', [status(thm)], ['64', '65'])).
% 0.44/0.66  thf('67', plain,
% 0.44/0.66      ((((k1_xboole_0) = (k1_relat_1 @ sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.66      inference('demod', [status(thm)], ['55', '63', '66'])).
% 0.44/0.66  thf('68', plain,
% 0.44/0.66      ((zip_tseitin_2 @ sk_C @ sk_C @ sk_B @ (k1_relat_1 @ sk_C))),
% 0.44/0.66      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.44/0.66  thf('69', plain,
% 0.44/0.66      (((zip_tseitin_2 @ sk_C @ sk_C @ sk_B @ k1_xboole_0))
% 0.44/0.66         <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.66      inference('sup+', [status(thm)], ['67', '68'])).
% 0.44/0.66  thf('70', plain,
% 0.44/0.66      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.44/0.66         ((r2_hidden @ X26 @ (k1_funct_2 @ X28 @ X27))
% 0.44/0.66          | ~ (zip_tseitin_2 @ X25 @ X26 @ X27 @ X28))),
% 0.44/0.66      inference('simplify', [status(thm)], ['45'])).
% 0.44/0.66  thf('71', plain,
% 0.44/0.66      (((r2_hidden @ sk_C @ (k1_funct_2 @ k1_xboole_0 @ sk_B)))
% 0.44/0.66         <= ((((sk_A) = (k1_xboole_0))))),
% 0.44/0.66      inference('sup-', [status(thm)], ['69', '70'])).
% 0.44/0.66  thf('72', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.44/0.66      inference('demod', [status(thm)], ['50', '71'])).
% 0.44/0.66  thf('73', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.44/0.66      inference('split', [status(esa)], ['9'])).
% 0.44/0.66  thf('74', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.44/0.66      inference('sat_resolution*', [status(thm)], ['72', '73'])).
% 0.44/0.66  thf('75', plain, ((r2_hidden @ sk_C @ (k1_funct_2 @ sk_A @ sk_B))),
% 0.44/0.66      inference('simpl_trail', [status(thm)], ['47', '74'])).
% 0.44/0.66  thf('76', plain, ($false), inference('demod', [status(thm)], ['0', '75'])).
% 0.44/0.66  
% 0.44/0.66  % SZS output end Refutation
% 0.44/0.66  
% 0.44/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
