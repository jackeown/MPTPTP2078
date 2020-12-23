%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yW9LYHDc9C

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 369 expanded)
%              Number of leaves         :   31 ( 117 expanded)
%              Depth                    :   13
%              Number of atoms          :  790 (5846 expanded)
%              Number of equality atoms :   32 ( 215 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_E ) @ sk_C )
    | ~ ( r2_hidden @ sk_E @ sk_A )
    | ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) )
   <= ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( ( k8_relset_1 @ X13 @ X14 @ X12 @ X15 )
        = ( k10_relat_1 @ X12 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 )
      = ( k10_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ sk_C ) )
   <= ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['1','4'])).

thf('6',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) )
    | ~ ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_E ) @ sk_C )
    | ~ ( r2_hidden @ sk_E @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 )
      = ( k10_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('8',plain,
    ( ( r2_hidden @ sk_E @ sk_A )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ sk_C ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['7','9'])).

thf(d13_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k10_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) )
                & ( r2_hidden @ ( k1_funct_1 @ A @ D ) @ B ) ) ) ) ) )).

thf('11',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X3
       != ( k10_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ X4 @ ( k1_relat_1 @ X2 ) )
      | ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_1])).

thf('12',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k10_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ X4 @ ( k1_relat_1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( ( r2_hidden @ sk_E @ ( k1_relat_1 @ sk_D_1 ) )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_relat_1 @ sk_D_1 ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ sk_B ),
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

thf('15',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ( X18
        = ( k1_relset_1 @ X18 @ X19 @ X20 ) )
      | ~ ( zip_tseitin_1 @ X20 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('16',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('18',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('19',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( zip_tseitin_0 @ X21 @ X22 )
      | ( zip_tseitin_1 @ X23 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('20',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('25',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('26',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['16','23','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('30',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('31',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r2_hidden @ sk_E @ sk_A )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['13','27','28','31'])).

thf('33',plain,
    ( ~ ( r2_hidden @ sk_E @ sk_A )
   <= ~ ( r2_hidden @ sk_E @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,
    ( ( r2_hidden @ sk_E @ sk_A )
    | ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ sk_C ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['7','9'])).

thf('36',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X3
       != ( k10_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X2 @ X4 ) @ X1 )
      | ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_1])).

thf('37',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k10_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X2 @ X4 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_E ) @ sk_C )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_relat_1 @ sk_D_1 ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('41',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_E ) @ sk_C )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_E ) @ sk_C )
   <= ~ ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_E ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('43',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_E ) @ sk_C )
    | ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['6','34','43'])).

thf('45',plain,(
    ~ ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['5','44'])).

thf('46',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_E ) @ sk_C )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_E ) @ sk_C )
   <= ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_E ) @ sk_C ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_E ) @ sk_C )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['46'])).

thf('49',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_E ) @ sk_C ),
    inference('sat_resolution*',[status(thm)],['6','34','43','48'])).

thf('50',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_E ) @ sk_C ),
    inference(simpl_trail,[status(thm)],['47','49'])).

thf('51',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['16','23','26'])).

thf('52',plain,(
    ! [X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ( X3
       != ( k10_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X2 @ X5 ) @ X1 )
      | ~ ( r2_hidden @ X5 @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_1])).

thf('53',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( r2_hidden @ X5 @ ( k1_relat_1 @ X2 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X2 @ X5 ) @ X1 )
      | ( r2_hidden @ X5 @ ( k10_relat_1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k10_relat_1 @ sk_D_1 @ X1 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ X1 )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k10_relat_1 @ sk_D_1 @ X1 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ sk_C ) )
    | ~ ( r2_hidden @ sk_E @ sk_A ) ),
    inference('sup-',[status(thm)],['50','57'])).

thf('59',plain,
    ( ( r2_hidden @ sk_E @ sk_A )
   <= ( r2_hidden @ sk_E @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('60',plain,
    ( ( r2_hidden @ sk_E @ sk_A )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['8'])).

thf('61',plain,(
    r2_hidden @ sk_E @ sk_A ),
    inference('sat_resolution*',[status(thm)],['6','34','43','60'])).

thf('62',plain,(
    r2_hidden @ sk_E @ sk_A ),
    inference(simpl_trail,[status(thm)],['59','61'])).

thf('63',plain,(
    r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['58','62'])).

thf('64',plain,(
    $false ),
    inference(demod,[status(thm)],['45','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yW9LYHDc9C
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:04:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.56  % Solved by: fo/fo7.sh
% 0.20/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.56  % done 103 iterations in 0.092s
% 0.20/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.56  % SZS output start Refutation
% 0.20/0.56  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.56  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.56  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.20/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.56  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.56  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.56  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.56  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.56  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.20/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.56  thf(t46_funct_2, conjecture,
% 0.20/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.56     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.56         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.56       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.56         ( ![E:$i]:
% 0.20/0.56           ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ B @ D @ C ) ) <=>
% 0.20/0.56             ( ( r2_hidden @ E @ A ) & 
% 0.20/0.56               ( r2_hidden @ ( k1_funct_1 @ D @ E ) @ C ) ) ) ) ) ))).
% 0.20/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.56    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.56        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.56            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.56          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.56            ( ![E:$i]:
% 0.20/0.56              ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ B @ D @ C ) ) <=>
% 0.20/0.56                ( ( r2_hidden @ E @ A ) & 
% 0.20/0.56                  ( r2_hidden @ ( k1_funct_1 @ D @ E ) @ C ) ) ) ) ) ) )),
% 0.20/0.56    inference('cnf.neg', [status(esa)], [t46_funct_2])).
% 0.20/0.56  thf('0', plain,
% 0.20/0.56      ((~ (r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_E) @ sk_C)
% 0.20/0.56        | ~ (r2_hidden @ sk_E @ sk_A)
% 0.20/0.56        | ~ (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('1', plain,
% 0.20/0.56      ((~ (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C)))
% 0.20/0.56         <= (~
% 0.20/0.56             ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))))),
% 0.20/0.56      inference('split', [status(esa)], ['0'])).
% 0.20/0.56  thf('2', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(redefinition_k8_relset_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.56       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.20/0.56  thf('3', plain,
% 0.20/0.56      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.20/0.56          | ((k8_relset_1 @ X13 @ X14 @ X12 @ X15) = (k10_relat_1 @ X12 @ X15)))),
% 0.20/0.56      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.20/0.56  thf('4', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)
% 0.20/0.56           = (k10_relat_1 @ sk_D_1 @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.56  thf('5', plain,
% 0.20/0.56      ((~ (r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ sk_C)))
% 0.20/0.56         <= (~
% 0.20/0.56             ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))))),
% 0.20/0.56      inference('demod', [status(thm)], ['1', '4'])).
% 0.20/0.56  thf('6', plain,
% 0.20/0.56      (~ ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))) | 
% 0.20/0.56       ~ ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_E) @ sk_C)) | 
% 0.20/0.56       ~ ((r2_hidden @ sk_E @ sk_A))),
% 0.20/0.56      inference('split', [status(esa)], ['0'])).
% 0.20/0.56  thf('7', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)
% 0.20/0.56           = (k10_relat_1 @ sk_D_1 @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.56  thf('8', plain,
% 0.20/0.56      (((r2_hidden @ sk_E @ sk_A)
% 0.20/0.56        | (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('9', plain,
% 0.20/0.56      (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C)))
% 0.20/0.56         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))))),
% 0.20/0.56      inference('split', [status(esa)], ['8'])).
% 0.20/0.56  thf('10', plain,
% 0.20/0.56      (((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ sk_C)))
% 0.20/0.56         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))))),
% 0.20/0.56      inference('sup+', [status(thm)], ['7', '9'])).
% 0.20/0.56  thf(d13_funct_1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.56       ( ![B:$i,C:$i]:
% 0.20/0.56         ( ( ( C ) = ( k10_relat_1 @ A @ B ) ) <=>
% 0.20/0.56           ( ![D:$i]:
% 0.20/0.56             ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.56               ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.20/0.56                 ( r2_hidden @ ( k1_funct_1 @ A @ D ) @ B ) ) ) ) ) ) ))).
% 0.20/0.56  thf('11', plain,
% 0.20/0.56      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.56         (((X3) != (k10_relat_1 @ X2 @ X1))
% 0.20/0.56          | (r2_hidden @ X4 @ (k1_relat_1 @ X2))
% 0.20/0.56          | ~ (r2_hidden @ X4 @ X3)
% 0.20/0.56          | ~ (v1_funct_1 @ X2)
% 0.20/0.56          | ~ (v1_relat_1 @ X2))),
% 0.20/0.56      inference('cnf', [status(esa)], [d13_funct_1])).
% 0.20/0.56  thf('12', plain,
% 0.20/0.56      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.20/0.56         (~ (v1_relat_1 @ X2)
% 0.20/0.56          | ~ (v1_funct_1 @ X2)
% 0.20/0.56          | ~ (r2_hidden @ X4 @ (k10_relat_1 @ X2 @ X1))
% 0.20/0.56          | (r2_hidden @ X4 @ (k1_relat_1 @ X2)))),
% 0.20/0.56      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.56  thf('13', plain,
% 0.20/0.56      ((((r2_hidden @ sk_E @ (k1_relat_1 @ sk_D_1))
% 0.20/0.56         | ~ (v1_funct_1 @ sk_D_1)
% 0.20/0.56         | ~ (v1_relat_1 @ sk_D_1)))
% 0.20/0.56         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['10', '12'])).
% 0.20/0.56  thf('14', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(d1_funct_2, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.56       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.56           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.20/0.56             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.56         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.56           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.20/0.56             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.20/0.56  thf(zf_stmt_1, axiom,
% 0.20/0.56    (![C:$i,B:$i,A:$i]:
% 0.20/0.56     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.20/0.56       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.56  thf('15', plain,
% 0.20/0.56      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.56         (~ (v1_funct_2 @ X20 @ X18 @ X19)
% 0.20/0.56          | ((X18) = (k1_relset_1 @ X18 @ X19 @ X20))
% 0.20/0.56          | ~ (zip_tseitin_1 @ X20 @ X19 @ X18))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.56  thf('16', plain,
% 0.20/0.56      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)
% 0.20/0.56        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_1)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.56  thf(zf_stmt_2, axiom,
% 0.20/0.56    (![B:$i,A:$i]:
% 0.20/0.56     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.56       ( zip_tseitin_0 @ B @ A ) ))).
% 0.20/0.56  thf('17', plain,
% 0.20/0.56      (![X16 : $i, X17 : $i]:
% 0.20/0.56         ((zip_tseitin_0 @ X16 @ X17) | ((X16) = (k1_xboole_0)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.56  thf('18', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.20/0.56  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.20/0.56  thf(zf_stmt_5, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.56       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.20/0.56         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.56           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.56             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.20/0.56  thf('19', plain,
% 0.20/0.56      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.56         (~ (zip_tseitin_0 @ X21 @ X22)
% 0.20/0.56          | (zip_tseitin_1 @ X23 @ X21 @ X22)
% 0.20/0.56          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21))))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.56  thf('20', plain,
% 0.20/0.56      (((zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)
% 0.20/0.56        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.56  thf('21', plain,
% 0.20/0.56      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['17', '20'])).
% 0.20/0.56  thf('22', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('23', plain, ((zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)),
% 0.20/0.56      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.20/0.56  thf('24', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.56       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.56  thf('25', plain,
% 0.20/0.56      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.56         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.20/0.56          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.20/0.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.56  thf('26', plain,
% 0.20/0.56      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.56  thf('27', plain, (((sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.20/0.56      inference('demod', [status(thm)], ['16', '23', '26'])).
% 0.20/0.56  thf('28', plain, ((v1_funct_1 @ sk_D_1)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('29', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(cc1_relset_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.56       ( v1_relat_1 @ C ) ))).
% 0.20/0.56  thf('30', plain,
% 0.20/0.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.56         ((v1_relat_1 @ X6)
% 0.20/0.56          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.20/0.56      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.56  thf('31', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.56      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.56  thf('32', plain,
% 0.20/0.56      (((r2_hidden @ sk_E @ sk_A))
% 0.20/0.56         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))))),
% 0.20/0.56      inference('demod', [status(thm)], ['13', '27', '28', '31'])).
% 0.20/0.56  thf('33', plain,
% 0.20/0.56      ((~ (r2_hidden @ sk_E @ sk_A)) <= (~ ((r2_hidden @ sk_E @ sk_A)))),
% 0.20/0.56      inference('split', [status(esa)], ['0'])).
% 0.20/0.56  thf('34', plain,
% 0.20/0.56      (((r2_hidden @ sk_E @ sk_A)) | 
% 0.20/0.56       ~ ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.56  thf('35', plain,
% 0.20/0.56      (((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ sk_C)))
% 0.20/0.56         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))))),
% 0.20/0.56      inference('sup+', [status(thm)], ['7', '9'])).
% 0.20/0.56  thf('36', plain,
% 0.20/0.56      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.56         (((X3) != (k10_relat_1 @ X2 @ X1))
% 0.20/0.56          | (r2_hidden @ (k1_funct_1 @ X2 @ X4) @ X1)
% 0.20/0.56          | ~ (r2_hidden @ X4 @ X3)
% 0.20/0.56          | ~ (v1_funct_1 @ X2)
% 0.20/0.56          | ~ (v1_relat_1 @ X2))),
% 0.20/0.56      inference('cnf', [status(esa)], [d13_funct_1])).
% 0.20/0.56  thf('37', plain,
% 0.20/0.56      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.20/0.56         (~ (v1_relat_1 @ X2)
% 0.20/0.56          | ~ (v1_funct_1 @ X2)
% 0.20/0.56          | ~ (r2_hidden @ X4 @ (k10_relat_1 @ X2 @ X1))
% 0.20/0.56          | (r2_hidden @ (k1_funct_1 @ X2 @ X4) @ X1))),
% 0.20/0.56      inference('simplify', [status(thm)], ['36'])).
% 0.20/0.56  thf('38', plain,
% 0.20/0.56      ((((r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_E) @ sk_C)
% 0.20/0.56         | ~ (v1_funct_1 @ sk_D_1)
% 0.20/0.56         | ~ (v1_relat_1 @ sk_D_1)))
% 0.20/0.56         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['35', '37'])).
% 0.20/0.56  thf('39', plain, ((v1_funct_1 @ sk_D_1)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('40', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.56      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.56  thf('41', plain,
% 0.20/0.56      (((r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_E) @ sk_C))
% 0.20/0.56         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))))),
% 0.20/0.56      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.20/0.56  thf('42', plain,
% 0.20/0.56      ((~ (r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_E) @ sk_C))
% 0.20/0.56         <= (~ ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_E) @ sk_C)))),
% 0.20/0.56      inference('split', [status(esa)], ['0'])).
% 0.20/0.56  thf('43', plain,
% 0.20/0.56      (((r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_E) @ sk_C)) | 
% 0.20/0.56       ~ ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.56  thf('44', plain,
% 0.20/0.56      (~ ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C)))),
% 0.20/0.56      inference('sat_resolution*', [status(thm)], ['6', '34', '43'])).
% 0.20/0.56  thf('45', plain, (~ (r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ sk_C))),
% 0.20/0.56      inference('simpl_trail', [status(thm)], ['5', '44'])).
% 0.20/0.56  thf('46', plain,
% 0.20/0.56      (((r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_E) @ sk_C)
% 0.20/0.56        | (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('47', plain,
% 0.20/0.56      (((r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_E) @ sk_C))
% 0.20/0.56         <= (((r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_E) @ sk_C)))),
% 0.20/0.56      inference('split', [status(esa)], ['46'])).
% 0.20/0.56  thf('48', plain,
% 0.20/0.56      (((r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_E) @ sk_C)) | 
% 0.20/0.56       ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C)))),
% 0.20/0.56      inference('split', [status(esa)], ['46'])).
% 0.20/0.56  thf('49', plain, (((r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_E) @ sk_C))),
% 0.20/0.56      inference('sat_resolution*', [status(thm)], ['6', '34', '43', '48'])).
% 0.20/0.56  thf('50', plain, ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_E) @ sk_C)),
% 0.20/0.56      inference('simpl_trail', [status(thm)], ['47', '49'])).
% 0.20/0.56  thf('51', plain, (((sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.20/0.56      inference('demod', [status(thm)], ['16', '23', '26'])).
% 0.20/0.56  thf('52', plain,
% 0.20/0.56      (![X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 0.20/0.56         (((X3) != (k10_relat_1 @ X2 @ X1))
% 0.20/0.56          | (r2_hidden @ X5 @ X3)
% 0.20/0.56          | ~ (r2_hidden @ (k1_funct_1 @ X2 @ X5) @ X1)
% 0.20/0.56          | ~ (r2_hidden @ X5 @ (k1_relat_1 @ X2))
% 0.20/0.56          | ~ (v1_funct_1 @ X2)
% 0.20/0.56          | ~ (v1_relat_1 @ X2))),
% 0.20/0.56      inference('cnf', [status(esa)], [d13_funct_1])).
% 0.20/0.56  thf('53', plain,
% 0.20/0.56      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.20/0.56         (~ (v1_relat_1 @ X2)
% 0.20/0.56          | ~ (v1_funct_1 @ X2)
% 0.20/0.56          | ~ (r2_hidden @ X5 @ (k1_relat_1 @ X2))
% 0.20/0.56          | ~ (r2_hidden @ (k1_funct_1 @ X2 @ X5) @ X1)
% 0.20/0.56          | (r2_hidden @ X5 @ (k10_relat_1 @ X2 @ X1)))),
% 0.20/0.56      inference('simplify', [status(thm)], ['52'])).
% 0.20/0.56  thf('54', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.56          | (r2_hidden @ X0 @ (k10_relat_1 @ sk_D_1 @ X1))
% 0.20/0.56          | ~ (r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ X1)
% 0.20/0.56          | ~ (v1_funct_1 @ sk_D_1)
% 0.20/0.56          | ~ (v1_relat_1 @ sk_D_1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['51', '53'])).
% 0.20/0.56  thf('55', plain, ((v1_funct_1 @ sk_D_1)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('56', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.56      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.56  thf('57', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.56          | (r2_hidden @ X0 @ (k10_relat_1 @ sk_D_1 @ X1))
% 0.20/0.56          | ~ (r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ X1))),
% 0.20/0.56      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.20/0.56  thf('58', plain,
% 0.20/0.56      (((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ sk_C))
% 0.20/0.56        | ~ (r2_hidden @ sk_E @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['50', '57'])).
% 0.20/0.56  thf('59', plain,
% 0.20/0.56      (((r2_hidden @ sk_E @ sk_A)) <= (((r2_hidden @ sk_E @ sk_A)))),
% 0.20/0.56      inference('split', [status(esa)], ['8'])).
% 0.20/0.56  thf('60', plain,
% 0.20/0.56      (((r2_hidden @ sk_E @ sk_A)) | 
% 0.20/0.56       ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C)))),
% 0.20/0.56      inference('split', [status(esa)], ['8'])).
% 0.20/0.56  thf('61', plain, (((r2_hidden @ sk_E @ sk_A))),
% 0.20/0.56      inference('sat_resolution*', [status(thm)], ['6', '34', '43', '60'])).
% 0.20/0.56  thf('62', plain, ((r2_hidden @ sk_E @ sk_A)),
% 0.20/0.56      inference('simpl_trail', [status(thm)], ['59', '61'])).
% 0.20/0.56  thf('63', plain, ((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ sk_C))),
% 0.20/0.56      inference('demod', [status(thm)], ['58', '62'])).
% 0.20/0.56  thf('64', plain, ($false), inference('demod', [status(thm)], ['45', '63'])).
% 0.20/0.56  
% 0.20/0.56  % SZS output end Refutation
% 0.20/0.56  
% 0.20/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
