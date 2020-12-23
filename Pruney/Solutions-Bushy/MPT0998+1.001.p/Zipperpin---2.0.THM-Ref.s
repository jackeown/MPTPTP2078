%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0998+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5ixHgK1SvG

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:51 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 369 expanded)
%              Number of leaves         :   31 ( 117 expanded)
%              Depth                    :   13
%              Number of atoms          :  790 (5846 expanded)
%              Number of equality atoms :   32 ( 215 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( ( k8_relset_1 @ X21 @ X22 @ X20 @ X23 )
        = ( k10_relat_1 @ X20 @ X23 ) ) ) ),
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
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X6
       != ( k10_relat_1 @ X5 @ X4 ) )
      | ( r2_hidden @ X7 @ ( k1_relat_1 @ X5 ) )
      | ~ ( r2_hidden @ X7 @ X6 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_1])).

thf('12',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k10_relat_1 @ X5 @ X4 ) )
      | ( r2_hidden @ X7 @ ( k1_relat_1 @ X5 ) ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_funct_2 @ X13 @ X11 @ X12 )
      | ( X11
        = ( k1_relset_1 @ X11 @ X12 @ X13 ) )
      | ~ ( zip_tseitin_1 @ X13 @ X12 @ X11 ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 )
      | ( X9 = k1_xboole_0 ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( zip_tseitin_0 @ X14 @ X15 )
      | ( zip_tseitin_1 @ X16 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X14 ) ) ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
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
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X6
       != ( k10_relat_1 @ X5 @ X4 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X5 @ X7 ) @ X4 )
      | ~ ( r2_hidden @ X7 @ X6 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_1])).

thf('37',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k10_relat_1 @ X5 @ X4 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X5 @ X7 ) @ X4 ) ) ),
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
    ! [X4: $i,X5: $i,X6: $i,X8: $i] :
      ( ( X6
       != ( k10_relat_1 @ X5 @ X4 ) )
      | ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X5 @ X8 ) @ X4 )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_1])).

thf('53',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X5 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X5 @ X8 ) @ X4 )
      | ( r2_hidden @ X8 @ ( k10_relat_1 @ X5 @ X4 ) ) ) ),
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
