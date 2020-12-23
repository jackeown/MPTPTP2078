%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.T63N5lAI5m

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:16 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 210 expanded)
%              Number of leaves         :   36 (  76 expanded)
%              Depth                    :   15
%              Number of atoms          :  817 (2389 expanded)
%              Number of equality atoms :   83 ( 217 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 )
      | ( X11 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 )
      | ( X11 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,(
    ! [X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 )
      | ( X11 = k1_xboole_0 ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( zip_tseitin_0 @ X16 @ X17 )
      | ( zip_tseitin_1 @ X18 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ( X13
        = ( k1_relset_1 @ X13 @ X14 @ X15 ) )
      | ~ ( zip_tseitin_1 @ X15 @ X14 @ X13 ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
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
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v5_relat_1 @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( ~ ( v5_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('33',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('34',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['31','34'])).

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

thf('36',plain,(
    ! [X19: $i,X20: $i,X21: $i,X23: $i] :
      ( ( zip_tseitin_2 @ X19 @ X21 @ X20 @ X23 )
      | ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ( X21 != X19 )
      | ( ( k1_relat_1 @ X19 )
       != X23 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('37',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 )
      | ( zip_tseitin_2 @ X19 @ X19 @ X20 @ ( k1_relat_1 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( zip_tseitin_2 @ sk_C @ sk_C @ sk_B @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['32','33'])).

thf('40',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    zip_tseitin_2 @ sk_C @ sk_C @ sk_B @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ( zip_tseitin_2 @ sk_C @ sk_C @ sk_B @ sk_A )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','41'])).

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

thf('43',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_2 @ X24 @ X25 @ X26 @ X27 )
      | ( r2_hidden @ X25 @ X28 )
      | ( X28
       != ( k1_funct_2 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('44',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( r2_hidden @ X25 @ ( k1_funct_2 @ X27 @ X26 ) )
      | ~ ( zip_tseitin_2 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( r2_hidden @ sk_C @ ( k1_funct_2 @ sk_A @ sk_B ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('47',plain,(
    ~ ( r2_hidden @ sk_C @ ( k1_funct_2 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ~ ( r2_hidden @ sk_C @ ( k1_funct_2 @ k1_xboole_0 @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('50',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v1_funct_2 @ sk_C @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ( X13
        = ( k1_relset_1 @ X13 @ X14 @ X15 ) )
      | ~ ( zip_tseitin_1 @ X15 @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('53',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( zip_tseitin_0 @ X16 @ X17 )
      | ( zip_tseitin_1 @ X18 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('58',plain,
    ( ( ( zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('60',plain,(
    ! [X11: $i] :
      ( zip_tseitin_0 @ X11 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','60'])).

thf('62',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('63',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('64',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C )
      = ( k1_relat_1 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','61','64'])).

thf('66',plain,(
    zip_tseitin_2 @ sk_C @ sk_C @ sk_B @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('67',plain,
    ( ( zip_tseitin_2 @ sk_C @ sk_C @ sk_B @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( r2_hidden @ X25 @ ( k1_funct_2 @ X27 @ X26 ) )
      | ~ ( zip_tseitin_2 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('69',plain,
    ( ( r2_hidden @ sk_C @ ( k1_funct_2 @ k1_xboole_0 @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['48','69'])).

thf('71',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('72',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['70','71'])).

thf('73',plain,(
    r2_hidden @ sk_C @ ( k1_funct_2 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['45','72'])).

thf('74',plain,(
    $false ),
    inference(demod,[status(thm)],['0','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.T63N5lAI5m
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:33:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.43/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.62  % Solved by: fo/fo7.sh
% 0.43/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.62  % done 193 iterations in 0.151s
% 0.43/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.62  % SZS output start Refutation
% 0.43/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.43/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.43/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.43/0.62  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.43/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.62  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 0.43/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.43/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.43/0.62  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $i > $o).
% 0.43/0.62  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.43/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.43/0.62  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.43/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.43/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.43/0.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.43/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.43/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.43/0.62  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.43/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.62  thf(t11_funct_2, conjecture,
% 0.43/0.62    (![A:$i,B:$i,C:$i]:
% 0.43/0.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.43/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.43/0.62       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.43/0.62         ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) ) ))).
% 0.43/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.62    (~( ![A:$i,B:$i,C:$i]:
% 0.43/0.62        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.43/0.62            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.43/0.62          ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.43/0.62            ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) ) ) )),
% 0.43/0.62    inference('cnf.neg', [status(esa)], [t11_funct_2])).
% 0.43/0.62  thf('0', plain, (~ (r2_hidden @ sk_C @ (k1_funct_2 @ sk_A @ sk_B))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(d1_funct_2, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i]:
% 0.43/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.43/0.62       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.43/0.62           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.43/0.62             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.43/0.62         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.43/0.62           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.43/0.62             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.43/0.62  thf(zf_stmt_1, axiom,
% 0.43/0.62    (![B:$i,A:$i]:
% 0.43/0.62     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.43/0.62       ( zip_tseitin_0 @ B @ A ) ))).
% 0.43/0.62  thf('1', plain,
% 0.43/0.62      (![X11 : $i, X12 : $i]:
% 0.43/0.62         ((zip_tseitin_0 @ X11 @ X12) | ((X11) = (k1_xboole_0)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.43/0.62  thf('2', plain,
% 0.43/0.62      (![X11 : $i, X12 : $i]:
% 0.43/0.62         ((zip_tseitin_0 @ X11 @ X12) | ((X11) = (k1_xboole_0)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.43/0.62  thf('3', plain,
% 0.43/0.62      (![X11 : $i, X12 : $i]:
% 0.43/0.62         ((zip_tseitin_0 @ X11 @ X12) | ((X11) = (k1_xboole_0)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.43/0.62  thf('4', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.62         (((X1) = (X0)) | (zip_tseitin_0 @ X0 @ X3) | (zip_tseitin_0 @ X1 @ X2))),
% 0.43/0.62      inference('sup+', [status(thm)], ['2', '3'])).
% 0.43/0.62  thf('5', plain,
% 0.43/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.43/0.62  thf(zf_stmt_3, axiom,
% 0.43/0.62    (![C:$i,B:$i,A:$i]:
% 0.43/0.62     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.43/0.62       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.43/0.62  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.43/0.62  thf(zf_stmt_5, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i]:
% 0.43/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.43/0.62       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.43/0.62         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.43/0.62           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.43/0.62             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.43/0.62  thf('6', plain,
% 0.43/0.62      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.43/0.62         (~ (zip_tseitin_0 @ X16 @ X17)
% 0.43/0.62          | (zip_tseitin_1 @ X18 @ X16 @ X17)
% 0.43/0.62          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16))))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.43/0.62  thf('7', plain,
% 0.43/0.62      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.43/0.62      inference('sup-', [status(thm)], ['5', '6'])).
% 0.43/0.62  thf('8', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((zip_tseitin_0 @ X1 @ X0)
% 0.43/0.62          | ((sk_B) = (X1))
% 0.43/0.62          | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.43/0.62      inference('sup-', [status(thm)], ['4', '7'])).
% 0.43/0.62  thf('9', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B) != (k1_xboole_0)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('10', plain,
% 0.43/0.62      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.43/0.62      inference('split', [status(esa)], ['9'])).
% 0.43/0.62  thf('11', plain,
% 0.43/0.62      ((![X0 : $i, X1 : $i]:
% 0.43/0.62          (((X0) != (k1_xboole_0))
% 0.43/0.62           | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.43/0.62           | (zip_tseitin_0 @ X0 @ X1)))
% 0.43/0.62         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['8', '10'])).
% 0.43/0.62  thf('12', plain,
% 0.43/0.62      ((![X1 : $i]:
% 0.43/0.62          ((zip_tseitin_0 @ k1_xboole_0 @ X1)
% 0.43/0.62           | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)))
% 0.43/0.62         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.43/0.62      inference('simplify', [status(thm)], ['11'])).
% 0.43/0.62  thf('13', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('14', plain,
% 0.43/0.62      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.43/0.62         (~ (v1_funct_2 @ X15 @ X13 @ X14)
% 0.43/0.62          | ((X13) = (k1_relset_1 @ X13 @ X14 @ X15))
% 0.43/0.62          | ~ (zip_tseitin_1 @ X15 @ X14 @ X13))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.43/0.62  thf('15', plain,
% 0.43/0.62      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.43/0.62        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['13', '14'])).
% 0.43/0.62  thf('16', plain,
% 0.43/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(redefinition_k1_relset_1, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i]:
% 0.43/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.43/0.62       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.43/0.62  thf('17', plain,
% 0.43/0.62      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.43/0.62         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 0.43/0.62          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.43/0.62      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.43/0.62  thf('18', plain,
% 0.43/0.62      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.43/0.62      inference('sup-', [status(thm)], ['16', '17'])).
% 0.43/0.62  thf('19', plain,
% 0.43/0.62      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.43/0.62      inference('demod', [status(thm)], ['15', '18'])).
% 0.43/0.62  thf('20', plain,
% 0.43/0.62      ((![X0 : $i]:
% 0.43/0.62          ((zip_tseitin_0 @ k1_xboole_0 @ X0) | ((sk_A) = (k1_relat_1 @ sk_C))))
% 0.43/0.62         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['12', '19'])).
% 0.43/0.62  thf('21', plain,
% 0.43/0.62      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.62          ((zip_tseitin_0 @ X0 @ X1)
% 0.43/0.62           | (zip_tseitin_0 @ X0 @ X2)
% 0.43/0.62           | ((sk_A) = (k1_relat_1 @ sk_C))))
% 0.43/0.62         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.43/0.62      inference('sup+', [status(thm)], ['1', '20'])).
% 0.43/0.62  thf('22', plain,
% 0.43/0.62      ((![X0 : $i, X1 : $i]:
% 0.43/0.62          (((sk_A) = (k1_relat_1 @ sk_C)) | (zip_tseitin_0 @ X1 @ X0)))
% 0.43/0.62         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.43/0.62      inference('condensation', [status(thm)], ['21'])).
% 0.43/0.62  thf('23', plain,
% 0.43/0.62      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.43/0.62      inference('sup-', [status(thm)], ['5', '6'])).
% 0.43/0.62  thf('24', plain,
% 0.43/0.62      (((((sk_A) = (k1_relat_1 @ sk_C)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)))
% 0.43/0.62         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['22', '23'])).
% 0.43/0.62  thf('25', plain,
% 0.43/0.62      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.43/0.62      inference('demod', [status(thm)], ['15', '18'])).
% 0.43/0.62  thf('26', plain,
% 0.43/0.62      ((((sk_A) = (k1_relat_1 @ sk_C))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.43/0.62      inference('clc', [status(thm)], ['24', '25'])).
% 0.43/0.62  thf('27', plain,
% 0.43/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(cc2_relset_1, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i]:
% 0.43/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.43/0.62       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.43/0.62  thf('28', plain,
% 0.43/0.62      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.43/0.62         ((v5_relat_1 @ X5 @ X7)
% 0.43/0.62          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.43/0.62      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.43/0.62  thf('29', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 0.43/0.62      inference('sup-', [status(thm)], ['27', '28'])).
% 0.43/0.62  thf(d19_relat_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( v1_relat_1 @ B ) =>
% 0.43/0.62       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.43/0.62  thf('30', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (~ (v5_relat_1 @ X0 @ X1)
% 0.43/0.62          | (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 0.43/0.62          | ~ (v1_relat_1 @ X0))),
% 0.43/0.62      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.43/0.62  thf('31', plain,
% 0.43/0.62      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 0.43/0.62      inference('sup-', [status(thm)], ['29', '30'])).
% 0.43/0.62  thf('32', plain,
% 0.43/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(cc1_relset_1, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i]:
% 0.43/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.43/0.62       ( v1_relat_1 @ C ) ))).
% 0.43/0.62  thf('33', plain,
% 0.43/0.62      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.43/0.62         ((v1_relat_1 @ X2)
% 0.43/0.62          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.43/0.62      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.43/0.62  thf('34', plain, ((v1_relat_1 @ sk_C)),
% 0.43/0.62      inference('sup-', [status(thm)], ['32', '33'])).
% 0.43/0.62  thf('35', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.43/0.62      inference('demod', [status(thm)], ['31', '34'])).
% 0.43/0.62  thf(d2_funct_2, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i]:
% 0.43/0.62     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 0.43/0.62       ( ![D:$i]:
% 0.43/0.62         ( ( r2_hidden @ D @ C ) <=>
% 0.43/0.62           ( ?[E:$i]:
% 0.43/0.62             ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) & ( ( D ) = ( E ) ) & 
% 0.43/0.62               ( ( k1_relat_1 @ E ) = ( A ) ) & 
% 0.43/0.62               ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) ) ) ) ) ))).
% 0.43/0.62  thf(zf_stmt_6, axiom,
% 0.43/0.62    (![E:$i,D:$i,B:$i,A:$i]:
% 0.43/0.62     ( ( zip_tseitin_2 @ E @ D @ B @ A ) <=>
% 0.43/0.62       ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) & 
% 0.43/0.62         ( ( k1_relat_1 @ E ) = ( A ) ) & ( ( D ) = ( E ) ) & 
% 0.43/0.62         ( v1_funct_1 @ E ) & ( v1_relat_1 @ E ) ) ))).
% 0.43/0.62  thf('36', plain,
% 0.43/0.62      (![X19 : $i, X20 : $i, X21 : $i, X23 : $i]:
% 0.43/0.62         ((zip_tseitin_2 @ X19 @ X21 @ X20 @ X23)
% 0.43/0.62          | ~ (v1_relat_1 @ X19)
% 0.43/0.62          | ~ (v1_funct_1 @ X19)
% 0.43/0.62          | ((X21) != (X19))
% 0.43/0.62          | ((k1_relat_1 @ X19) != (X23))
% 0.43/0.62          | ~ (r1_tarski @ (k2_relat_1 @ X19) @ X20))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.43/0.62  thf('37', plain,
% 0.43/0.62      (![X19 : $i, X20 : $i]:
% 0.43/0.62         (~ (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 0.43/0.62          | ~ (v1_funct_1 @ X19)
% 0.43/0.62          | ~ (v1_relat_1 @ X19)
% 0.43/0.62          | (zip_tseitin_2 @ X19 @ X19 @ X20 @ (k1_relat_1 @ X19)))),
% 0.43/0.62      inference('simplify', [status(thm)], ['36'])).
% 0.43/0.62  thf('38', plain,
% 0.43/0.62      (((zip_tseitin_2 @ sk_C @ sk_C @ sk_B @ (k1_relat_1 @ sk_C))
% 0.43/0.62        | ~ (v1_relat_1 @ sk_C)
% 0.43/0.62        | ~ (v1_funct_1 @ sk_C))),
% 0.43/0.62      inference('sup-', [status(thm)], ['35', '37'])).
% 0.43/0.62  thf('39', plain, ((v1_relat_1 @ sk_C)),
% 0.43/0.62      inference('sup-', [status(thm)], ['32', '33'])).
% 0.43/0.62  thf('40', plain, ((v1_funct_1 @ sk_C)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('41', plain,
% 0.43/0.62      ((zip_tseitin_2 @ sk_C @ sk_C @ sk_B @ (k1_relat_1 @ sk_C))),
% 0.43/0.62      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.43/0.62  thf('42', plain,
% 0.43/0.62      (((zip_tseitin_2 @ sk_C @ sk_C @ sk_B @ sk_A))
% 0.43/0.62         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.43/0.62      inference('sup+', [status(thm)], ['26', '41'])).
% 0.43/0.62  thf(zf_stmt_7, type, zip_tseitin_2 : $i > $i > $i > $i > $o).
% 0.43/0.62  thf(zf_stmt_8, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i]:
% 0.43/0.62     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 0.43/0.62       ( ![D:$i]:
% 0.43/0.62         ( ( r2_hidden @ D @ C ) <=>
% 0.43/0.62           ( ?[E:$i]: ( zip_tseitin_2 @ E @ D @ B @ A ) ) ) ) ))).
% 0.43/0.62  thf('43', plain,
% 0.43/0.62      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.43/0.62         (~ (zip_tseitin_2 @ X24 @ X25 @ X26 @ X27)
% 0.43/0.62          | (r2_hidden @ X25 @ X28)
% 0.43/0.62          | ((X28) != (k1_funct_2 @ X27 @ X26)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.43/0.62  thf('44', plain,
% 0.43/0.62      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.43/0.62         ((r2_hidden @ X25 @ (k1_funct_2 @ X27 @ X26))
% 0.43/0.62          | ~ (zip_tseitin_2 @ X24 @ X25 @ X26 @ X27))),
% 0.43/0.62      inference('simplify', [status(thm)], ['43'])).
% 0.43/0.62  thf('45', plain,
% 0.43/0.62      (((r2_hidden @ sk_C @ (k1_funct_2 @ sk_A @ sk_B)))
% 0.43/0.62         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['42', '44'])).
% 0.43/0.62  thf('46', plain,
% 0.43/0.62      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.43/0.62      inference('split', [status(esa)], ['9'])).
% 0.43/0.62  thf('47', plain, (~ (r2_hidden @ sk_C @ (k1_funct_2 @ sk_A @ sk_B))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('48', plain,
% 0.43/0.62      ((~ (r2_hidden @ sk_C @ (k1_funct_2 @ k1_xboole_0 @ sk_B)))
% 0.43/0.62         <= ((((sk_A) = (k1_xboole_0))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['46', '47'])).
% 0.43/0.62  thf('49', plain,
% 0.43/0.62      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.43/0.62      inference('split', [status(esa)], ['9'])).
% 0.43/0.62  thf('50', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('51', plain,
% 0.43/0.62      (((v1_funct_2 @ sk_C @ k1_xboole_0 @ sk_B))
% 0.43/0.62         <= ((((sk_A) = (k1_xboole_0))))),
% 0.43/0.62      inference('sup+', [status(thm)], ['49', '50'])).
% 0.43/0.62  thf('52', plain,
% 0.43/0.62      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.43/0.62         (~ (v1_funct_2 @ X15 @ X13 @ X14)
% 0.43/0.62          | ((X13) = (k1_relset_1 @ X13 @ X14 @ X15))
% 0.43/0.62          | ~ (zip_tseitin_1 @ X15 @ X14 @ X13))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.43/0.62  thf('53', plain,
% 0.43/0.62      (((~ (zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0)
% 0.43/0.62         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C))))
% 0.43/0.62         <= ((((sk_A) = (k1_xboole_0))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['51', '52'])).
% 0.43/0.62  thf('54', plain,
% 0.43/0.62      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.43/0.62      inference('split', [status(esa)], ['9'])).
% 0.43/0.62  thf('55', plain,
% 0.43/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('56', plain,
% 0.43/0.62      (((m1_subset_1 @ sk_C @ 
% 0.43/0.62         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.43/0.62         <= ((((sk_A) = (k1_xboole_0))))),
% 0.43/0.62      inference('sup+', [status(thm)], ['54', '55'])).
% 0.43/0.62  thf('57', plain,
% 0.43/0.62      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.43/0.62         (~ (zip_tseitin_0 @ X16 @ X17)
% 0.43/0.62          | (zip_tseitin_1 @ X18 @ X16 @ X17)
% 0.43/0.62          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16))))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.43/0.62  thf('58', plain,
% 0.43/0.62      ((((zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0)
% 0.43/0.62         | ~ (zip_tseitin_0 @ sk_B @ k1_xboole_0)))
% 0.43/0.62         <= ((((sk_A) = (k1_xboole_0))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['56', '57'])).
% 0.43/0.62  thf('59', plain,
% 0.43/0.62      (![X11 : $i, X12 : $i]:
% 0.43/0.62         ((zip_tseitin_0 @ X11 @ X12) | ((X12) != (k1_xboole_0)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.43/0.62  thf('60', plain, (![X11 : $i]: (zip_tseitin_0 @ X11 @ k1_xboole_0)),
% 0.43/0.62      inference('simplify', [status(thm)], ['59'])).
% 0.43/0.62  thf('61', plain,
% 0.43/0.62      (((zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0))
% 0.43/0.62         <= ((((sk_A) = (k1_xboole_0))))),
% 0.43/0.62      inference('demod', [status(thm)], ['58', '60'])).
% 0.43/0.62  thf('62', plain,
% 0.43/0.62      (((m1_subset_1 @ sk_C @ 
% 0.43/0.62         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.43/0.62         <= ((((sk_A) = (k1_xboole_0))))),
% 0.43/0.62      inference('sup+', [status(thm)], ['54', '55'])).
% 0.43/0.62  thf('63', plain,
% 0.43/0.62      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.43/0.62         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 0.43/0.62          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.43/0.62      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.43/0.62  thf('64', plain,
% 0.43/0.62      ((((k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C) = (k1_relat_1 @ sk_C)))
% 0.43/0.62         <= ((((sk_A) = (k1_xboole_0))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['62', '63'])).
% 0.43/0.62  thf('65', plain,
% 0.43/0.62      ((((k1_xboole_0) = (k1_relat_1 @ sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.43/0.62      inference('demod', [status(thm)], ['53', '61', '64'])).
% 0.43/0.62  thf('66', plain,
% 0.43/0.62      ((zip_tseitin_2 @ sk_C @ sk_C @ sk_B @ (k1_relat_1 @ sk_C))),
% 0.43/0.62      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.43/0.62  thf('67', plain,
% 0.43/0.62      (((zip_tseitin_2 @ sk_C @ sk_C @ sk_B @ k1_xboole_0))
% 0.43/0.62         <= ((((sk_A) = (k1_xboole_0))))),
% 0.43/0.62      inference('sup+', [status(thm)], ['65', '66'])).
% 0.43/0.62  thf('68', plain,
% 0.43/0.62      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.43/0.62         ((r2_hidden @ X25 @ (k1_funct_2 @ X27 @ X26))
% 0.43/0.62          | ~ (zip_tseitin_2 @ X24 @ X25 @ X26 @ X27))),
% 0.43/0.62      inference('simplify', [status(thm)], ['43'])).
% 0.43/0.62  thf('69', plain,
% 0.43/0.62      (((r2_hidden @ sk_C @ (k1_funct_2 @ k1_xboole_0 @ sk_B)))
% 0.43/0.62         <= ((((sk_A) = (k1_xboole_0))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['67', '68'])).
% 0.43/0.62  thf('70', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.43/0.62      inference('demod', [status(thm)], ['48', '69'])).
% 0.43/0.62  thf('71', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.43/0.62      inference('split', [status(esa)], ['9'])).
% 0.43/0.62  thf('72', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.43/0.62      inference('sat_resolution*', [status(thm)], ['70', '71'])).
% 0.43/0.62  thf('73', plain, ((r2_hidden @ sk_C @ (k1_funct_2 @ sk_A @ sk_B))),
% 0.43/0.62      inference('simpl_trail', [status(thm)], ['45', '72'])).
% 0.43/0.62  thf('74', plain, ($false), inference('demod', [status(thm)], ['0', '73'])).
% 0.43/0.62  
% 0.43/0.62  % SZS output end Refutation
% 0.43/0.62  
% 0.43/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
