%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YmhWC8GUMB

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:32 EST 2020

% Result     : Theorem 3.15s
% Output     : Refutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :  199 (1067 expanded)
%              Number of leaves         :   42 ( 334 expanded)
%              Depth                    :   29
%              Number of atoms          : 1473 (13586 expanded)
%              Number of equality atoms :  113 ( 722 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(t113_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ! [E: $i] :
                ( ( m1_subset_1 @ E @ A )
               => ( ( k1_funct_1 @ C @ E )
                  = ( k1_funct_1 @ D @ E ) ) )
           => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ B )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
           => ( ! [E: $i] :
                  ( ( m1_subset_1 @ E @ A )
                 => ( ( k1_funct_1 @ C @ E )
                    = ( k1_funct_1 @ D @ E ) ) )
             => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t113_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('2',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( r2_relset_1 @ X30 @ X31 @ X29 @ X32 )
      | ( X29 != X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('3',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( r2_relset_1 @ X30 @ X31 @ X32 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_D @ sk_D ),
    inference('sup-',[status(thm)],['1','3'])).

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

thf('5',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('7',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['5','7'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('9',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('10',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('11',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( m1_subset_1 @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_B @ sk_C_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('14',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X10 @ X9 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('15',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ ( sk_B @ sk_C_1 ) )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('17',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ ( sk_B @ sk_C_1 ) )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('20',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C_1 )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( k1_xboole_0
        = ( sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('24',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X21 @ X22 )
      | ~ ( r1_tarski @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_C_1 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C_1 )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ~ ( r1_tarski @ sk_C_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['5','7'])).

thf('29',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('30',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('31',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['27','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('35',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('36',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ( X35
        = ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('40',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('42',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('43',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['40','43'])).

thf('45',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['37','44'])).

thf('46',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( sk_C_1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ X0 @ sk_D )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['4','49'])).

thf('51',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('52',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('55',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['40','43'])).

thf('57',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('59',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('62',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( m1_subset_1 @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( m1_subset_1 @ ( sk_B @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X10 @ X9 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('67',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( sk_B @ sk_D ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['60','67'])).

thf('69',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('70',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( sk_B @ sk_D ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ ( sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['57','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('73',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( k1_xboole_0
      = ( sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('75',plain,
    ( ~ ( r1_tarski @ sk_D @ k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( r1_tarski @ sk_D @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('79',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('81',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['78','81'])).

thf('83',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( r1_tarski @ sk_D @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','82'])).

thf('84',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(clc,[status(thm)],['76','83'])).

thf('85',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['50','84'])).

thf('86',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_D @ sk_D ),
    inference('sup-',[status(thm)],['1','3'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['27','32'])).

thf('88',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('90',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['87','90'])).

thf('92',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ( X35
        = ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('94',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('97',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['94','97'])).

thf('99',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['91','98'])).

thf('100',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) )
      | ( sk_C_1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ X0 @ sk_D )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['86','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('106',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('107',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['94','97'])).

thf('109',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( sk_B @ sk_D ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('111',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ ( sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('113',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( k1_xboole_0
      = ( sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('115',plain,
    ( ~ ( r1_tarski @ sk_D @ k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( r1_tarski @ sk_D @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('118',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['78','81'])).

thf('119',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( r1_tarski @ sk_D @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(clc,[status(thm)],['116','119'])).

thf('121',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['104','120'])).

thf(t9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k1_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ! [C: $i] :
                  ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                 => ( ( k1_funct_1 @ A @ C )
                    = ( k1_funct_1 @ B @ C ) ) ) )
           => ( A = B ) ) ) ) )).

thf('122',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ( X20 = X19 )
      | ( r2_hidden @ ( sk_C @ X19 @ X20 ) @ ( k1_relat_1 @ X20 ) )
      | ( ( k1_relat_1 @ X20 )
       != ( k1_relat_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('125',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v1_relat_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('126',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['104','120'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_A )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['123','126','127','128'])).

thf('130',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['85','129'])).

thf('131',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v1_relat_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('133',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['130','133','134'])).

thf('136',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference(simplify,[status(thm)],['135'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('137',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ X11 @ X12 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('138',plain,
    ( ( sk_C_1 = sk_D )
    | ( m1_subset_1 @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X41: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ X41 )
        = ( k1_funct_1 @ sk_D @ X41 ) )
      | ~ ( m1_subset_1 @ X41 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( sk_C_1 = sk_D )
    | ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,
    ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ),
    inference(condensation,[status(thm)],['140'])).

thf('142',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ( X20 = X19 )
      | ( ( k1_funct_1 @ X20 @ ( sk_C @ X19 @ X20 ) )
       != ( k1_funct_1 @ X19 @ ( sk_C @ X19 @ X20 ) ) )
      | ( ( k1_relat_1 @ X20 )
       != ( k1_relat_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('143',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_1 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['124','125'])).

thf('145',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['104','120'])).

thf('147',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['50','84'])).

thf('148',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['131','132'])).

thf('150',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference(demod,[status(thm)],['143','144','145','146','147','148','149'])).

thf('151',plain,(
    sk_C_1 = sk_D ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( r2_relset_1 @ X30 @ X31 @ X32 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('154',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    $false ),
    inference(demod,[status(thm)],['0','151','154'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YmhWC8GUMB
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:59:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 3.15/3.33  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.15/3.33  % Solved by: fo/fo7.sh
% 3.15/3.33  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.15/3.33  % done 2308 iterations in 2.886s
% 3.15/3.33  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.15/3.33  % SZS output start Refutation
% 3.15/3.33  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.15/3.33  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.15/3.33  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.15/3.33  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 3.15/3.33  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.15/3.33  thf(sk_B_1_type, type, sk_B_1: $i).
% 3.15/3.33  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.15/3.33  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.15/3.33  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.15/3.33  thf(sk_D_type, type, sk_D: $i).
% 3.15/3.33  thf(sk_C_1_type, type, sk_C_1: $i).
% 3.15/3.33  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.15/3.33  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.15/3.33  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.15/3.33  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.15/3.33  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.15/3.33  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.15/3.33  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.15/3.33  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.15/3.33  thf(sk_B_type, type, sk_B: $i > $i).
% 3.15/3.33  thf(sk_A_type, type, sk_A: $i).
% 3.15/3.33  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.15/3.33  thf(t113_funct_2, conjecture,
% 3.15/3.33    (![A:$i,B:$i,C:$i]:
% 3.15/3.33     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.15/3.33         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.15/3.33       ( ![D:$i]:
% 3.15/3.33         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.15/3.33             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.15/3.33           ( ( ![E:$i]:
% 3.15/3.33               ( ( m1_subset_1 @ E @ A ) =>
% 3.15/3.33                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 3.15/3.33             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 3.15/3.33  thf(zf_stmt_0, negated_conjecture,
% 3.15/3.33    (~( ![A:$i,B:$i,C:$i]:
% 3.15/3.33        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.15/3.33            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.15/3.33          ( ![D:$i]:
% 3.15/3.33            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.15/3.33                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.15/3.33              ( ( ![E:$i]:
% 3.15/3.33                  ( ( m1_subset_1 @ E @ A ) =>
% 3.15/3.33                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 3.15/3.33                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 3.15/3.33    inference('cnf.neg', [status(esa)], [t113_funct_2])).
% 3.15/3.33  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)),
% 3.15/3.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.15/3.33  thf('1', plain,
% 3.15/3.33      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.15/3.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.15/3.33  thf(redefinition_r2_relset_1, axiom,
% 3.15/3.33    (![A:$i,B:$i,C:$i,D:$i]:
% 3.15/3.33     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.15/3.33         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.15/3.33       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.15/3.33  thf('2', plain,
% 3.15/3.33      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 3.15/3.33         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 3.15/3.33          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 3.15/3.33          | (r2_relset_1 @ X30 @ X31 @ X29 @ X32)
% 3.15/3.33          | ((X29) != (X32)))),
% 3.15/3.33      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.15/3.33  thf('3', plain,
% 3.15/3.33      (![X30 : $i, X31 : $i, X32 : $i]:
% 3.15/3.33         ((r2_relset_1 @ X30 @ X31 @ X32 @ X32)
% 3.15/3.33          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 3.15/3.33      inference('simplify', [status(thm)], ['2'])).
% 3.15/3.33  thf('4', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_D @ sk_D)),
% 3.15/3.33      inference('sup-', [status(thm)], ['1', '3'])).
% 3.15/3.33  thf(d1_funct_2, axiom,
% 3.15/3.33    (![A:$i,B:$i,C:$i]:
% 3.15/3.33     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.15/3.33       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.15/3.33           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.15/3.33             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.15/3.33         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.15/3.33           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.15/3.33             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.15/3.33  thf(zf_stmt_1, axiom,
% 3.15/3.33    (![B:$i,A:$i]:
% 3.15/3.33     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.15/3.33       ( zip_tseitin_0 @ B @ A ) ))).
% 3.15/3.33  thf('5', plain,
% 3.15/3.33      (![X33 : $i, X34 : $i]:
% 3.15/3.33         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 3.15/3.33      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.15/3.33  thf(t113_zfmisc_1, axiom,
% 3.15/3.33    (![A:$i,B:$i]:
% 3.15/3.33     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.15/3.33       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.15/3.33  thf('6', plain,
% 3.15/3.33      (![X6 : $i, X7 : $i]:
% 3.15/3.33         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 3.15/3.33      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.15/3.33  thf('7', plain,
% 3.15/3.33      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 3.15/3.33      inference('simplify', [status(thm)], ['6'])).
% 3.15/3.33  thf('8', plain,
% 3.15/3.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.15/3.33         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 3.15/3.33      inference('sup+', [status(thm)], ['5', '7'])).
% 3.15/3.33  thf(d1_xboole_0, axiom,
% 3.15/3.33    (![A:$i]:
% 3.15/3.33     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 3.15/3.33  thf('9', plain,
% 3.15/3.33      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 3.15/3.33      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.15/3.33  thf('10', plain,
% 3.15/3.33      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.15/3.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.15/3.33  thf(t4_subset, axiom,
% 3.15/3.33    (![A:$i,B:$i,C:$i]:
% 3.15/3.33     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 3.15/3.33       ( m1_subset_1 @ A @ C ) ))).
% 3.15/3.33  thf('11', plain,
% 3.15/3.33      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.15/3.33         (~ (r2_hidden @ X16 @ X17)
% 3.15/3.33          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 3.15/3.33          | (m1_subset_1 @ X16 @ X18))),
% 3.15/3.33      inference('cnf', [status(esa)], [t4_subset])).
% 3.15/3.33  thf('12', plain,
% 3.15/3.33      (![X0 : $i]:
% 3.15/3.33         ((m1_subset_1 @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 3.15/3.33          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 3.15/3.33      inference('sup-', [status(thm)], ['10', '11'])).
% 3.15/3.33  thf('13', plain,
% 3.15/3.33      (((v1_xboole_0 @ sk_C_1)
% 3.15/3.33        | (m1_subset_1 @ (sk_B @ sk_C_1) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.15/3.33      inference('sup-', [status(thm)], ['9', '12'])).
% 3.15/3.33  thf(d2_subset_1, axiom,
% 3.15/3.33    (![A:$i,B:$i]:
% 3.15/3.33     ( ( ( v1_xboole_0 @ A ) =>
% 3.15/3.33         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 3.15/3.33       ( ( ~( v1_xboole_0 @ A ) ) =>
% 3.15/3.33         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 3.15/3.33  thf('14', plain,
% 3.15/3.33      (![X9 : $i, X10 : $i]:
% 3.15/3.33         (~ (m1_subset_1 @ X10 @ X9)
% 3.15/3.33          | (v1_xboole_0 @ X10)
% 3.15/3.33          | ~ (v1_xboole_0 @ X9))),
% 3.15/3.33      inference('cnf', [status(esa)], [d2_subset_1])).
% 3.15/3.33  thf('15', plain,
% 3.15/3.33      (((v1_xboole_0 @ sk_C_1)
% 3.15/3.33        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 3.15/3.33        | (v1_xboole_0 @ (sk_B @ sk_C_1)))),
% 3.15/3.33      inference('sup-', [status(thm)], ['13', '14'])).
% 3.15/3.33  thf('16', plain,
% 3.15/3.33      (![X0 : $i]:
% 3.15/3.33         (~ (v1_xboole_0 @ k1_xboole_0)
% 3.15/3.33          | (zip_tseitin_0 @ sk_B_1 @ X0)
% 3.15/3.33          | (v1_xboole_0 @ (sk_B @ sk_C_1))
% 3.15/3.33          | (v1_xboole_0 @ sk_C_1))),
% 3.15/3.33      inference('sup-', [status(thm)], ['8', '15'])).
% 3.15/3.33  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.15/3.33  thf('17', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.15/3.33      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.15/3.33  thf('18', plain,
% 3.15/3.33      (![X0 : $i]:
% 3.15/3.33         ((zip_tseitin_0 @ sk_B_1 @ X0)
% 3.15/3.33          | (v1_xboole_0 @ (sk_B @ sk_C_1))
% 3.15/3.33          | (v1_xboole_0 @ sk_C_1))),
% 3.15/3.33      inference('demod', [status(thm)], ['16', '17'])).
% 3.15/3.33  thf('19', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.15/3.33      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.15/3.33  thf(t8_boole, axiom,
% 3.15/3.33    (![A:$i,B:$i]:
% 3.15/3.33     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 3.15/3.33  thf('20', plain,
% 3.15/3.33      (![X3 : $i, X4 : $i]:
% 3.15/3.33         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 3.15/3.33      inference('cnf', [status(esa)], [t8_boole])).
% 3.15/3.33  thf('21', plain,
% 3.15/3.33      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.15/3.33      inference('sup-', [status(thm)], ['19', '20'])).
% 3.15/3.33  thf('22', plain,
% 3.15/3.33      (![X0 : $i]:
% 3.15/3.33         ((v1_xboole_0 @ sk_C_1)
% 3.15/3.33          | (zip_tseitin_0 @ sk_B_1 @ X0)
% 3.15/3.33          | ((k1_xboole_0) = (sk_B @ sk_C_1)))),
% 3.15/3.33      inference('sup-', [status(thm)], ['18', '21'])).
% 3.15/3.33  thf('23', plain,
% 3.15/3.33      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 3.15/3.33      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.15/3.33  thf(t7_ordinal1, axiom,
% 3.15/3.33    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.15/3.33  thf('24', plain,
% 3.15/3.33      (![X21 : $i, X22 : $i]:
% 3.15/3.33         (~ (r2_hidden @ X21 @ X22) | ~ (r1_tarski @ X22 @ X21))),
% 3.15/3.33      inference('cnf', [status(esa)], [t7_ordinal1])).
% 3.15/3.33  thf('25', plain,
% 3.15/3.33      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 3.15/3.33      inference('sup-', [status(thm)], ['23', '24'])).
% 3.15/3.33  thf('26', plain,
% 3.15/3.33      (![X0 : $i]:
% 3.15/3.33         (~ (r1_tarski @ sk_C_1 @ k1_xboole_0)
% 3.15/3.33          | (zip_tseitin_0 @ sk_B_1 @ X0)
% 3.15/3.33          | (v1_xboole_0 @ sk_C_1)
% 3.15/3.33          | (v1_xboole_0 @ sk_C_1))),
% 3.15/3.33      inference('sup-', [status(thm)], ['22', '25'])).
% 3.15/3.33  thf('27', plain,
% 3.15/3.33      (![X0 : $i]:
% 3.15/3.33         ((v1_xboole_0 @ sk_C_1)
% 3.15/3.33          | (zip_tseitin_0 @ sk_B_1 @ X0)
% 3.15/3.33          | ~ (r1_tarski @ sk_C_1 @ k1_xboole_0))),
% 3.15/3.33      inference('simplify', [status(thm)], ['26'])).
% 3.15/3.33  thf('28', plain,
% 3.15/3.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.15/3.33         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 3.15/3.33      inference('sup+', [status(thm)], ['5', '7'])).
% 3.15/3.33  thf('29', plain,
% 3.15/3.33      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.15/3.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.15/3.33  thf(t3_subset, axiom,
% 3.15/3.33    (![A:$i,B:$i]:
% 3.15/3.33     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.15/3.33  thf('30', plain,
% 3.15/3.33      (![X13 : $i, X14 : $i]:
% 3.15/3.33         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 3.15/3.33      inference('cnf', [status(esa)], [t3_subset])).
% 3.15/3.33  thf('31', plain, ((r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 3.15/3.33      inference('sup-', [status(thm)], ['29', '30'])).
% 3.15/3.33  thf('32', plain,
% 3.15/3.33      (![X0 : $i]:
% 3.15/3.33         ((r1_tarski @ sk_C_1 @ k1_xboole_0) | (zip_tseitin_0 @ sk_B_1 @ X0))),
% 3.15/3.33      inference('sup+', [status(thm)], ['28', '31'])).
% 3.15/3.33  thf('33', plain,
% 3.15/3.33      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_C_1))),
% 3.15/3.33      inference('clc', [status(thm)], ['27', '32'])).
% 3.15/3.33  thf('34', plain,
% 3.15/3.33      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.15/3.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.15/3.33  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.15/3.33  thf(zf_stmt_3, axiom,
% 3.15/3.33    (![C:$i,B:$i,A:$i]:
% 3.15/3.33     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.15/3.33       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.15/3.33  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 3.15/3.33  thf(zf_stmt_5, axiom,
% 3.15/3.33    (![A:$i,B:$i,C:$i]:
% 3.15/3.33     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.15/3.33       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.15/3.33         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.15/3.33           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.15/3.33             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.15/3.33  thf('35', plain,
% 3.15/3.33      (![X38 : $i, X39 : $i, X40 : $i]:
% 3.15/3.33         (~ (zip_tseitin_0 @ X38 @ X39)
% 3.15/3.34          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 3.15/3.34          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 3.15/3.34      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.15/3.34  thf('36', plain,
% 3.15/3.34      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 3.15/3.34        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 3.15/3.34      inference('sup-', [status(thm)], ['34', '35'])).
% 3.15/3.34  thf('37', plain,
% 3.15/3.34      (((v1_xboole_0 @ sk_C_1) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 3.15/3.34      inference('sup-', [status(thm)], ['33', '36'])).
% 3.15/3.34  thf('38', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 3.15/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.15/3.34  thf('39', plain,
% 3.15/3.34      (![X35 : $i, X36 : $i, X37 : $i]:
% 3.15/3.34         (~ (v1_funct_2 @ X37 @ X35 @ X36)
% 3.15/3.34          | ((X35) = (k1_relset_1 @ X35 @ X36 @ X37))
% 3.15/3.34          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 3.15/3.34      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.15/3.34  thf('40', plain,
% 3.15/3.34      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 3.15/3.34        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 3.15/3.34      inference('sup-', [status(thm)], ['38', '39'])).
% 3.15/3.34  thf('41', plain,
% 3.15/3.34      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.15/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.15/3.34  thf(redefinition_k1_relset_1, axiom,
% 3.15/3.34    (![A:$i,B:$i,C:$i]:
% 3.15/3.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.15/3.34       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.15/3.34  thf('42', plain,
% 3.15/3.34      (![X26 : $i, X27 : $i, X28 : $i]:
% 3.15/3.34         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 3.15/3.34          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 3.15/3.34      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.15/3.34  thf('43', plain,
% 3.15/3.34      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 3.15/3.34      inference('sup-', [status(thm)], ['41', '42'])).
% 3.15/3.34  thf('44', plain,
% 3.15/3.34      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 3.15/3.34        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.15/3.34      inference('demod', [status(thm)], ['40', '43'])).
% 3.15/3.34  thf('45', plain, (((v1_xboole_0 @ sk_C_1) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.15/3.34      inference('sup-', [status(thm)], ['37', '44'])).
% 3.15/3.34  thf('46', plain,
% 3.15/3.34      (![X3 : $i, X4 : $i]:
% 3.15/3.34         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 3.15/3.34      inference('cnf', [status(esa)], [t8_boole])).
% 3.15/3.34  thf('47', plain,
% 3.15/3.34      (![X0 : $i]:
% 3.15/3.34         (((sk_A) = (k1_relat_1 @ sk_D))
% 3.15/3.34          | ((sk_C_1) = (X0))
% 3.15/3.34          | ~ (v1_xboole_0 @ X0))),
% 3.15/3.34      inference('sup-', [status(thm)], ['45', '46'])).
% 3.15/3.34  thf('48', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)),
% 3.15/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.15/3.34  thf('49', plain,
% 3.15/3.34      (![X0 : $i]:
% 3.15/3.34         (~ (r2_relset_1 @ sk_A @ sk_B_1 @ X0 @ sk_D)
% 3.15/3.34          | ~ (v1_xboole_0 @ X0)
% 3.15/3.34          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.15/3.34      inference('sup-', [status(thm)], ['47', '48'])).
% 3.15/3.34  thf('50', plain, ((((sk_A) = (k1_relat_1 @ sk_D)) | ~ (v1_xboole_0 @ sk_D))),
% 3.15/3.34      inference('sup-', [status(thm)], ['4', '49'])).
% 3.15/3.34  thf('51', plain,
% 3.15/3.34      (![X33 : $i, X34 : $i]:
% 3.15/3.34         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 3.15/3.34      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.15/3.34  thf('52', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.15/3.34      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.15/3.34  thf('53', plain,
% 3.15/3.34      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 3.15/3.34      inference('sup+', [status(thm)], ['51', '52'])).
% 3.15/3.34  thf('54', plain,
% 3.15/3.34      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 3.15/3.34        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 3.15/3.34      inference('sup-', [status(thm)], ['34', '35'])).
% 3.15/3.34  thf('55', plain,
% 3.15/3.34      (((v1_xboole_0 @ sk_B_1) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 3.15/3.34      inference('sup-', [status(thm)], ['53', '54'])).
% 3.15/3.34  thf('56', plain,
% 3.15/3.34      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 3.15/3.34        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.15/3.34      inference('demod', [status(thm)], ['40', '43'])).
% 3.15/3.34  thf('57', plain, (((v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.15/3.34      inference('sup-', [status(thm)], ['55', '56'])).
% 3.15/3.34  thf('58', plain,
% 3.15/3.34      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.15/3.34      inference('sup-', [status(thm)], ['19', '20'])).
% 3.15/3.34  thf('59', plain,
% 3.15/3.34      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 3.15/3.34      inference('simplify', [status(thm)], ['6'])).
% 3.15/3.34  thf('60', plain,
% 3.15/3.34      (![X0 : $i, X1 : $i]:
% 3.15/3.34         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.15/3.34      inference('sup+', [status(thm)], ['58', '59'])).
% 3.15/3.34  thf('61', plain,
% 3.15/3.34      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 3.15/3.34      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.15/3.34  thf('62', plain,
% 3.15/3.34      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.15/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.15/3.34  thf('63', plain,
% 3.15/3.34      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.15/3.34         (~ (r2_hidden @ X16 @ X17)
% 3.15/3.34          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 3.15/3.34          | (m1_subset_1 @ X16 @ X18))),
% 3.15/3.34      inference('cnf', [status(esa)], [t4_subset])).
% 3.15/3.34  thf('64', plain,
% 3.15/3.34      (![X0 : $i]:
% 3.15/3.34         ((m1_subset_1 @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 3.15/3.34          | ~ (r2_hidden @ X0 @ sk_D))),
% 3.15/3.34      inference('sup-', [status(thm)], ['62', '63'])).
% 3.15/3.34  thf('65', plain,
% 3.15/3.34      (((v1_xboole_0 @ sk_D)
% 3.15/3.34        | (m1_subset_1 @ (sk_B @ sk_D) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.15/3.34      inference('sup-', [status(thm)], ['61', '64'])).
% 3.15/3.34  thf('66', plain,
% 3.15/3.34      (![X9 : $i, X10 : $i]:
% 3.15/3.34         (~ (m1_subset_1 @ X10 @ X9)
% 3.15/3.34          | (v1_xboole_0 @ X10)
% 3.15/3.34          | ~ (v1_xboole_0 @ X9))),
% 3.15/3.34      inference('cnf', [status(esa)], [d2_subset_1])).
% 3.15/3.34  thf('67', plain,
% 3.15/3.34      (((v1_xboole_0 @ sk_D)
% 3.15/3.34        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 3.15/3.34        | (v1_xboole_0 @ (sk_B @ sk_D)))),
% 3.15/3.34      inference('sup-', [status(thm)], ['65', '66'])).
% 3.15/3.34  thf('68', plain,
% 3.15/3.34      ((~ (v1_xboole_0 @ k1_xboole_0)
% 3.15/3.34        | ~ (v1_xboole_0 @ sk_B_1)
% 3.15/3.34        | (v1_xboole_0 @ (sk_B @ sk_D))
% 3.15/3.34        | (v1_xboole_0 @ sk_D))),
% 3.15/3.34      inference('sup-', [status(thm)], ['60', '67'])).
% 3.15/3.34  thf('69', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.15/3.34      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.15/3.34  thf('70', plain,
% 3.15/3.34      ((~ (v1_xboole_0 @ sk_B_1)
% 3.15/3.34        | (v1_xboole_0 @ (sk_B @ sk_D))
% 3.15/3.34        | (v1_xboole_0 @ sk_D))),
% 3.15/3.34      inference('demod', [status(thm)], ['68', '69'])).
% 3.15/3.34  thf('71', plain,
% 3.15/3.34      ((((sk_A) = (k1_relat_1 @ sk_D))
% 3.15/3.34        | (v1_xboole_0 @ sk_D)
% 3.15/3.34        | (v1_xboole_0 @ (sk_B @ sk_D)))),
% 3.15/3.34      inference('sup-', [status(thm)], ['57', '70'])).
% 3.15/3.34  thf('72', plain,
% 3.15/3.34      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.15/3.34      inference('sup-', [status(thm)], ['19', '20'])).
% 3.15/3.34  thf('73', plain,
% 3.15/3.34      (((v1_xboole_0 @ sk_D)
% 3.15/3.34        | ((sk_A) = (k1_relat_1 @ sk_D))
% 3.15/3.34        | ((k1_xboole_0) = (sk_B @ sk_D)))),
% 3.15/3.34      inference('sup-', [status(thm)], ['71', '72'])).
% 3.15/3.34  thf('74', plain,
% 3.15/3.34      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 3.15/3.34      inference('sup-', [status(thm)], ['23', '24'])).
% 3.15/3.34  thf('75', plain,
% 3.15/3.34      ((~ (r1_tarski @ sk_D @ k1_xboole_0)
% 3.15/3.34        | ((sk_A) = (k1_relat_1 @ sk_D))
% 3.15/3.34        | (v1_xboole_0 @ sk_D)
% 3.15/3.34        | (v1_xboole_0 @ sk_D))),
% 3.15/3.34      inference('sup-', [status(thm)], ['73', '74'])).
% 3.15/3.34  thf('76', plain,
% 3.15/3.34      (((v1_xboole_0 @ sk_D)
% 3.15/3.34        | ((sk_A) = (k1_relat_1 @ sk_D))
% 3.15/3.34        | ~ (r1_tarski @ sk_D @ k1_xboole_0))),
% 3.15/3.34      inference('simplify', [status(thm)], ['75'])).
% 3.15/3.34  thf('77', plain, (((v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.15/3.34      inference('sup-', [status(thm)], ['55', '56'])).
% 3.15/3.34  thf('78', plain,
% 3.15/3.34      (![X0 : $i, X1 : $i]:
% 3.15/3.34         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.15/3.34      inference('sup+', [status(thm)], ['58', '59'])).
% 3.15/3.34  thf('79', plain,
% 3.15/3.34      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.15/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.15/3.34  thf('80', plain,
% 3.15/3.34      (![X13 : $i, X14 : $i]:
% 3.15/3.34         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 3.15/3.34      inference('cnf', [status(esa)], [t3_subset])).
% 3.15/3.34  thf('81', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 3.15/3.34      inference('sup-', [status(thm)], ['79', '80'])).
% 3.15/3.34  thf('82', plain,
% 3.15/3.34      (((r1_tarski @ sk_D @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_B_1))),
% 3.15/3.34      inference('sup+', [status(thm)], ['78', '81'])).
% 3.15/3.34  thf('83', plain,
% 3.15/3.34      ((((sk_A) = (k1_relat_1 @ sk_D)) | (r1_tarski @ sk_D @ k1_xboole_0))),
% 3.15/3.34      inference('sup-', [status(thm)], ['77', '82'])).
% 3.15/3.34  thf('84', plain, ((((sk_A) = (k1_relat_1 @ sk_D)) | (v1_xboole_0 @ sk_D))),
% 3.15/3.34      inference('clc', [status(thm)], ['76', '83'])).
% 3.15/3.34  thf('85', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 3.15/3.34      inference('clc', [status(thm)], ['50', '84'])).
% 3.15/3.34  thf('86', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_D @ sk_D)),
% 3.15/3.34      inference('sup-', [status(thm)], ['1', '3'])).
% 3.15/3.34  thf('87', plain,
% 3.15/3.34      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_C_1))),
% 3.15/3.34      inference('clc', [status(thm)], ['27', '32'])).
% 3.15/3.34  thf('88', plain,
% 3.15/3.34      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.15/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.15/3.34  thf('89', plain,
% 3.15/3.34      (![X38 : $i, X39 : $i, X40 : $i]:
% 3.15/3.34         (~ (zip_tseitin_0 @ X38 @ X39)
% 3.15/3.34          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 3.15/3.34          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 3.15/3.34      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.15/3.34  thf('90', plain,
% 3.15/3.34      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 3.15/3.34        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 3.15/3.34      inference('sup-', [status(thm)], ['88', '89'])).
% 3.15/3.34  thf('91', plain,
% 3.15/3.34      (((v1_xboole_0 @ sk_C_1) | (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A))),
% 3.15/3.34      inference('sup-', [status(thm)], ['87', '90'])).
% 3.15/3.34  thf('92', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 3.15/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.15/3.34  thf('93', plain,
% 3.15/3.34      (![X35 : $i, X36 : $i, X37 : $i]:
% 3.15/3.34         (~ (v1_funct_2 @ X37 @ X35 @ X36)
% 3.15/3.34          | ((X35) = (k1_relset_1 @ X35 @ X36 @ X37))
% 3.15/3.34          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 3.15/3.34      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.15/3.34  thf('94', plain,
% 3.15/3.34      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 3.15/3.34        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 3.15/3.34      inference('sup-', [status(thm)], ['92', '93'])).
% 3.15/3.34  thf('95', plain,
% 3.15/3.34      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.15/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.15/3.34  thf('96', plain,
% 3.15/3.34      (![X26 : $i, X27 : $i, X28 : $i]:
% 3.15/3.34         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 3.15/3.34          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 3.15/3.34      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.15/3.34  thf('97', plain,
% 3.15/3.34      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 3.15/3.34      inference('sup-', [status(thm)], ['95', '96'])).
% 3.15/3.34  thf('98', plain,
% 3.15/3.34      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 3.15/3.34        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 3.15/3.34      inference('demod', [status(thm)], ['94', '97'])).
% 3.15/3.34  thf('99', plain,
% 3.15/3.34      (((v1_xboole_0 @ sk_C_1) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 3.15/3.34      inference('sup-', [status(thm)], ['91', '98'])).
% 3.15/3.34  thf('100', plain,
% 3.15/3.34      (![X3 : $i, X4 : $i]:
% 3.15/3.34         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 3.15/3.34      inference('cnf', [status(esa)], [t8_boole])).
% 3.15/3.34  thf('101', plain,
% 3.15/3.34      (![X0 : $i]:
% 3.15/3.34         (((sk_A) = (k1_relat_1 @ sk_C_1))
% 3.15/3.34          | ((sk_C_1) = (X0))
% 3.15/3.34          | ~ (v1_xboole_0 @ X0))),
% 3.15/3.34      inference('sup-', [status(thm)], ['99', '100'])).
% 3.15/3.34  thf('102', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)),
% 3.15/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.15/3.34  thf('103', plain,
% 3.15/3.34      (![X0 : $i]:
% 3.15/3.34         (~ (r2_relset_1 @ sk_A @ sk_B_1 @ X0 @ sk_D)
% 3.15/3.34          | ~ (v1_xboole_0 @ X0)
% 3.15/3.34          | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 3.15/3.34      inference('sup-', [status(thm)], ['101', '102'])).
% 3.15/3.34  thf('104', plain,
% 3.15/3.34      ((((sk_A) = (k1_relat_1 @ sk_C_1)) | ~ (v1_xboole_0 @ sk_D))),
% 3.15/3.34      inference('sup-', [status(thm)], ['86', '103'])).
% 3.15/3.34  thf('105', plain,
% 3.15/3.34      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 3.15/3.34      inference('sup+', [status(thm)], ['51', '52'])).
% 3.15/3.34  thf('106', plain,
% 3.15/3.34      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 3.15/3.34        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 3.15/3.34      inference('sup-', [status(thm)], ['88', '89'])).
% 3.15/3.34  thf('107', plain,
% 3.15/3.34      (((v1_xboole_0 @ sk_B_1) | (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A))),
% 3.15/3.34      inference('sup-', [status(thm)], ['105', '106'])).
% 3.15/3.34  thf('108', plain,
% 3.15/3.34      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 3.15/3.34        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 3.15/3.34      inference('demod', [status(thm)], ['94', '97'])).
% 3.15/3.34  thf('109', plain,
% 3.15/3.34      (((v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 3.15/3.34      inference('sup-', [status(thm)], ['107', '108'])).
% 3.15/3.34  thf('110', plain,
% 3.15/3.34      ((~ (v1_xboole_0 @ sk_B_1)
% 3.15/3.34        | (v1_xboole_0 @ (sk_B @ sk_D))
% 3.15/3.34        | (v1_xboole_0 @ sk_D))),
% 3.15/3.34      inference('demod', [status(thm)], ['68', '69'])).
% 3.15/3.34  thf('111', plain,
% 3.15/3.34      ((((sk_A) = (k1_relat_1 @ sk_C_1))
% 3.15/3.34        | (v1_xboole_0 @ sk_D)
% 3.15/3.34        | (v1_xboole_0 @ (sk_B @ sk_D)))),
% 3.15/3.34      inference('sup-', [status(thm)], ['109', '110'])).
% 3.15/3.34  thf('112', plain,
% 3.15/3.34      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.15/3.34      inference('sup-', [status(thm)], ['19', '20'])).
% 3.15/3.34  thf('113', plain,
% 3.15/3.34      (((v1_xboole_0 @ sk_D)
% 3.15/3.34        | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 3.15/3.34        | ((k1_xboole_0) = (sk_B @ sk_D)))),
% 3.15/3.34      inference('sup-', [status(thm)], ['111', '112'])).
% 3.15/3.34  thf('114', plain,
% 3.15/3.34      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 3.15/3.34      inference('sup-', [status(thm)], ['23', '24'])).
% 3.15/3.34  thf('115', plain,
% 3.15/3.34      ((~ (r1_tarski @ sk_D @ k1_xboole_0)
% 3.15/3.34        | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 3.15/3.34        | (v1_xboole_0 @ sk_D)
% 3.15/3.34        | (v1_xboole_0 @ sk_D))),
% 3.15/3.34      inference('sup-', [status(thm)], ['113', '114'])).
% 3.15/3.34  thf('116', plain,
% 3.15/3.34      (((v1_xboole_0 @ sk_D)
% 3.15/3.34        | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 3.15/3.34        | ~ (r1_tarski @ sk_D @ k1_xboole_0))),
% 3.15/3.34      inference('simplify', [status(thm)], ['115'])).
% 3.15/3.34  thf('117', plain,
% 3.15/3.34      (((v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 3.15/3.34      inference('sup-', [status(thm)], ['107', '108'])).
% 3.15/3.34  thf('118', plain,
% 3.15/3.34      (((r1_tarski @ sk_D @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_B_1))),
% 3.15/3.34      inference('sup+', [status(thm)], ['78', '81'])).
% 3.15/3.34  thf('119', plain,
% 3.15/3.34      ((((sk_A) = (k1_relat_1 @ sk_C_1)) | (r1_tarski @ sk_D @ k1_xboole_0))),
% 3.15/3.34      inference('sup-', [status(thm)], ['117', '118'])).
% 3.15/3.34  thf('120', plain,
% 3.15/3.34      ((((sk_A) = (k1_relat_1 @ sk_C_1)) | (v1_xboole_0 @ sk_D))),
% 3.15/3.34      inference('clc', [status(thm)], ['116', '119'])).
% 3.15/3.34  thf('121', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 3.15/3.34      inference('clc', [status(thm)], ['104', '120'])).
% 3.15/3.34  thf(t9_funct_1, axiom,
% 3.15/3.34    (![A:$i]:
% 3.15/3.34     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.15/3.34       ( ![B:$i]:
% 3.15/3.34         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.15/3.34           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 3.15/3.34               ( ![C:$i]:
% 3.15/3.34                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 3.15/3.34                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 3.15/3.34             ( ( A ) = ( B ) ) ) ) ) ))).
% 3.15/3.34  thf('122', plain,
% 3.15/3.34      (![X19 : $i, X20 : $i]:
% 3.15/3.34         (~ (v1_relat_1 @ X19)
% 3.15/3.34          | ~ (v1_funct_1 @ X19)
% 3.15/3.34          | ((X20) = (X19))
% 3.15/3.34          | (r2_hidden @ (sk_C @ X19 @ X20) @ (k1_relat_1 @ X20))
% 3.15/3.34          | ((k1_relat_1 @ X20) != (k1_relat_1 @ X19))
% 3.15/3.34          | ~ (v1_funct_1 @ X20)
% 3.15/3.34          | ~ (v1_relat_1 @ X20))),
% 3.15/3.34      inference('cnf', [status(esa)], [t9_funct_1])).
% 3.15/3.34  thf('123', plain,
% 3.15/3.34      (![X0 : $i]:
% 3.15/3.34         (((sk_A) != (k1_relat_1 @ X0))
% 3.15/3.34          | ~ (v1_relat_1 @ sk_C_1)
% 3.15/3.34          | ~ (v1_funct_1 @ sk_C_1)
% 3.15/3.34          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 3.15/3.34          | ((sk_C_1) = (X0))
% 3.15/3.34          | ~ (v1_funct_1 @ X0)
% 3.15/3.34          | ~ (v1_relat_1 @ X0))),
% 3.15/3.34      inference('sup-', [status(thm)], ['121', '122'])).
% 3.15/3.34  thf('124', plain,
% 3.15/3.34      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.15/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.15/3.34  thf(cc1_relset_1, axiom,
% 3.15/3.34    (![A:$i,B:$i,C:$i]:
% 3.15/3.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.15/3.34       ( v1_relat_1 @ C ) ))).
% 3.15/3.34  thf('125', plain,
% 3.15/3.34      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.15/3.34         ((v1_relat_1 @ X23)
% 3.15/3.34          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 3.15/3.34      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.15/3.34  thf('126', plain, ((v1_relat_1 @ sk_C_1)),
% 3.15/3.34      inference('sup-', [status(thm)], ['124', '125'])).
% 3.15/3.34  thf('127', plain, ((v1_funct_1 @ sk_C_1)),
% 3.15/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.15/3.34  thf('128', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 3.15/3.34      inference('clc', [status(thm)], ['104', '120'])).
% 3.15/3.34  thf('129', plain,
% 3.15/3.34      (![X0 : $i]:
% 3.15/3.34         (((sk_A) != (k1_relat_1 @ X0))
% 3.15/3.34          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_A)
% 3.15/3.34          | ((sk_C_1) = (X0))
% 3.15/3.34          | ~ (v1_funct_1 @ X0)
% 3.15/3.34          | ~ (v1_relat_1 @ X0))),
% 3.15/3.34      inference('demod', [status(thm)], ['123', '126', '127', '128'])).
% 3.15/3.34  thf('130', plain,
% 3.15/3.34      ((((sk_A) != (sk_A))
% 3.15/3.34        | ~ (v1_relat_1 @ sk_D)
% 3.15/3.34        | ~ (v1_funct_1 @ sk_D)
% 3.15/3.34        | ((sk_C_1) = (sk_D))
% 3.15/3.34        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 3.15/3.34      inference('sup-', [status(thm)], ['85', '129'])).
% 3.15/3.34  thf('131', plain,
% 3.15/3.34      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.15/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.15/3.34  thf('132', plain,
% 3.15/3.34      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.15/3.34         ((v1_relat_1 @ X23)
% 3.15/3.34          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 3.15/3.34      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.15/3.34  thf('133', plain, ((v1_relat_1 @ sk_D)),
% 3.15/3.34      inference('sup-', [status(thm)], ['131', '132'])).
% 3.15/3.34  thf('134', plain, ((v1_funct_1 @ sk_D)),
% 3.15/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.15/3.34  thf('135', plain,
% 3.15/3.34      ((((sk_A) != (sk_A))
% 3.15/3.34        | ((sk_C_1) = (sk_D))
% 3.15/3.34        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 3.15/3.34      inference('demod', [status(thm)], ['130', '133', '134'])).
% 3.15/3.34  thf('136', plain,
% 3.15/3.34      (((r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A) | ((sk_C_1) = (sk_D)))),
% 3.15/3.34      inference('simplify', [status(thm)], ['135'])).
% 3.15/3.34  thf(t1_subset, axiom,
% 3.15/3.34    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 3.15/3.34  thf('137', plain,
% 3.15/3.34      (![X11 : $i, X12 : $i]:
% 3.15/3.34         ((m1_subset_1 @ X11 @ X12) | ~ (r2_hidden @ X11 @ X12))),
% 3.15/3.34      inference('cnf', [status(esa)], [t1_subset])).
% 3.15/3.34  thf('138', plain,
% 3.15/3.34      ((((sk_C_1) = (sk_D)) | (m1_subset_1 @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 3.15/3.34      inference('sup-', [status(thm)], ['136', '137'])).
% 3.15/3.34  thf('139', plain,
% 3.15/3.34      (![X41 : $i]:
% 3.15/3.34         (((k1_funct_1 @ sk_C_1 @ X41) = (k1_funct_1 @ sk_D @ X41))
% 3.15/3.34          | ~ (m1_subset_1 @ X41 @ sk_A))),
% 3.15/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.15/3.34  thf('140', plain,
% 3.15/3.34      ((((sk_C_1) = (sk_D))
% 3.15/3.34        | ((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 3.15/3.34            = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))))),
% 3.15/3.34      inference('sup-', [status(thm)], ['138', '139'])).
% 3.15/3.34  thf('141', plain,
% 3.15/3.34      (((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 3.15/3.34         = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))),
% 3.15/3.34      inference('condensation', [status(thm)], ['140'])).
% 3.15/3.34  thf('142', plain,
% 3.15/3.34      (![X19 : $i, X20 : $i]:
% 3.15/3.34         (~ (v1_relat_1 @ X19)
% 3.15/3.34          | ~ (v1_funct_1 @ X19)
% 3.15/3.34          | ((X20) = (X19))
% 3.15/3.34          | ((k1_funct_1 @ X20 @ (sk_C @ X19 @ X20))
% 3.15/3.34              != (k1_funct_1 @ X19 @ (sk_C @ X19 @ X20)))
% 3.15/3.34          | ((k1_relat_1 @ X20) != (k1_relat_1 @ X19))
% 3.15/3.34          | ~ (v1_funct_1 @ X20)
% 3.15/3.34          | ~ (v1_relat_1 @ X20))),
% 3.15/3.34      inference('cnf', [status(esa)], [t9_funct_1])).
% 3.15/3.34  thf('143', plain,
% 3.15/3.34      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 3.15/3.34          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 3.15/3.34        | ~ (v1_relat_1 @ sk_C_1)
% 3.15/3.34        | ~ (v1_funct_1 @ sk_C_1)
% 3.15/3.34        | ((k1_relat_1 @ sk_C_1) != (k1_relat_1 @ sk_D))
% 3.15/3.34        | ((sk_C_1) = (sk_D))
% 3.15/3.34        | ~ (v1_funct_1 @ sk_D)
% 3.15/3.34        | ~ (v1_relat_1 @ sk_D))),
% 3.15/3.34      inference('sup-', [status(thm)], ['141', '142'])).
% 3.15/3.34  thf('144', plain, ((v1_relat_1 @ sk_C_1)),
% 3.15/3.34      inference('sup-', [status(thm)], ['124', '125'])).
% 3.15/3.34  thf('145', plain, ((v1_funct_1 @ sk_C_1)),
% 3.15/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.15/3.34  thf('146', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 3.15/3.34      inference('clc', [status(thm)], ['104', '120'])).
% 3.15/3.34  thf('147', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 3.15/3.34      inference('clc', [status(thm)], ['50', '84'])).
% 3.15/3.34  thf('148', plain, ((v1_funct_1 @ sk_D)),
% 3.15/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.15/3.34  thf('149', plain, ((v1_relat_1 @ sk_D)),
% 3.15/3.34      inference('sup-', [status(thm)], ['131', '132'])).
% 3.15/3.34  thf('150', plain,
% 3.15/3.34      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 3.15/3.34          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 3.15/3.34        | ((sk_A) != (sk_A))
% 3.15/3.34        | ((sk_C_1) = (sk_D)))),
% 3.15/3.34      inference('demod', [status(thm)],
% 3.15/3.34                ['143', '144', '145', '146', '147', '148', '149'])).
% 3.15/3.34  thf('151', plain, (((sk_C_1) = (sk_D))),
% 3.15/3.34      inference('simplify', [status(thm)], ['150'])).
% 3.15/3.34  thf('152', plain,
% 3.15/3.34      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.15/3.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.15/3.34  thf('153', plain,
% 3.15/3.34      (![X30 : $i, X31 : $i, X32 : $i]:
% 3.15/3.34         ((r2_relset_1 @ X30 @ X31 @ X32 @ X32)
% 3.15/3.34          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 3.15/3.34      inference('simplify', [status(thm)], ['2'])).
% 3.15/3.34  thf('154', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_C_1)),
% 3.15/3.34      inference('sup-', [status(thm)], ['152', '153'])).
% 3.15/3.34  thf('155', plain, ($false),
% 3.15/3.34      inference('demod', [status(thm)], ['0', '151', '154'])).
% 3.15/3.34  
% 3.15/3.34  % SZS output end Refutation
% 3.15/3.34  
% 3.15/3.34  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
