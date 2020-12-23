%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XIsCw2XqhR

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:56 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 390 expanded)
%              Number of leaves         :   32 ( 124 expanded)
%              Depth                    :   13
%              Number of atoms          :  804 (5944 expanded)
%              Number of equality atoms :   32 ( 215 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

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
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( ( k8_relset_1 @ X14 @ X15 @ X13 @ X16 )
        = ( k10_relat_1 @ X13 @ X16 ) ) ) ),
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
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X7
       != ( k10_relat_1 @ X6 @ X5 ) )
      | ( r2_hidden @ X8 @ ( k1_relat_1 @ X6 ) )
      | ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_1])).

thf('12',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k10_relat_1 @ X6 @ X5 ) )
      | ( r2_hidden @ X8 @ ( k1_relat_1 @ X6 ) ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ( X19
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('32',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('33',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( r2_hidden @ sk_E @ sk_A )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['13','27','28','33'])).

thf('35',plain,
    ( ~ ( r2_hidden @ sk_E @ sk_A )
   <= ~ ( r2_hidden @ sk_E @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('36',plain,
    ( ( r2_hidden @ sk_E @ sk_A )
    | ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ sk_C ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['7','9'])).

thf('38',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X7
       != ( k10_relat_1 @ X6 @ X5 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X6 @ X8 ) @ X5 )
      | ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_1])).

thf('39',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k10_relat_1 @ X6 @ X5 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X6 @ X8 ) @ X5 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_E ) @ sk_C )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_relat_1 @ sk_D_1 ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['31','32'])).

thf('43',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_E ) @ sk_C )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_E ) @ sk_C )
   <= ~ ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_E ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_E ) @ sk_C )
    | ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['6','36','45'])).

thf('47',plain,(
    ~ ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['5','46'])).

thf('48',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_E ) @ sk_C )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_E ) @ sk_C )
   <= ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_E ) @ sk_C ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_E ) @ sk_C )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['48'])).

thf('51',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_E ) @ sk_C ),
    inference('sat_resolution*',[status(thm)],['6','36','45','50'])).

thf('52',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_E ) @ sk_C ),
    inference(simpl_trail,[status(thm)],['49','51'])).

thf('53',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['16','23','26'])).

thf('54',plain,(
    ! [X5: $i,X6: $i,X7: $i,X9: $i] :
      ( ( X7
       != ( k10_relat_1 @ X6 @ X5 ) )
      | ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X6 @ X9 ) @ X5 )
      | ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_1])).

thf('55',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ X6 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X6 @ X9 ) @ X5 )
      | ( r2_hidden @ X9 @ ( k10_relat_1 @ X6 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k10_relat_1 @ sk_D_1 @ X1 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ X1 )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['53','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['31','32'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k10_relat_1 @ sk_D_1 @ X1 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ sk_C ) )
    | ~ ( r2_hidden @ sk_E @ sk_A ) ),
    inference('sup-',[status(thm)],['52','59'])).

thf('61',plain,
    ( ( r2_hidden @ sk_E @ sk_A )
   <= ( r2_hidden @ sk_E @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('62',plain,
    ( ( r2_hidden @ sk_E @ sk_A )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['8'])).

thf('63',plain,(
    r2_hidden @ sk_E @ sk_A ),
    inference('sat_resolution*',[status(thm)],['6','36','45','62'])).

thf('64',plain,(
    r2_hidden @ sk_E @ sk_A ),
    inference(simpl_trail,[status(thm)],['61','63'])).

thf('65',plain,(
    r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','64'])).

thf('66',plain,(
    $false ),
    inference(demod,[status(thm)],['47','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XIsCw2XqhR
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:30:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.46/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.67  % Solved by: fo/fo7.sh
% 0.46/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.67  % done 119 iterations in 0.187s
% 0.46/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.67  % SZS output start Refutation
% 0.46/0.67  thf(sk_E_type, type, sk_E: $i).
% 0.46/0.67  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.46/0.67  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.67  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.46/0.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.67  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.46/0.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.67  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.67  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.46/0.67  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.46/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.67  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.46/0.67  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.46/0.67  thf(t46_funct_2, conjecture,
% 0.46/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.67     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.46/0.67         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.67       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.46/0.67         ( ![E:$i]:
% 0.46/0.67           ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ B @ D @ C ) ) <=>
% 0.46/0.67             ( ( r2_hidden @ E @ A ) & 
% 0.46/0.67               ( r2_hidden @ ( k1_funct_1 @ D @ E ) @ C ) ) ) ) ) ))).
% 0.46/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.67    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.67        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.46/0.67            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.67          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.46/0.67            ( ![E:$i]:
% 0.46/0.67              ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ B @ D @ C ) ) <=>
% 0.46/0.67                ( ( r2_hidden @ E @ A ) & 
% 0.46/0.67                  ( r2_hidden @ ( k1_funct_1 @ D @ E ) @ C ) ) ) ) ) ) )),
% 0.46/0.67    inference('cnf.neg', [status(esa)], [t46_funct_2])).
% 0.46/0.67  thf('0', plain,
% 0.46/0.67      ((~ (r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_E) @ sk_C)
% 0.46/0.67        | ~ (r2_hidden @ sk_E @ sk_A)
% 0.46/0.67        | ~ (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('1', plain,
% 0.46/0.67      ((~ (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C)))
% 0.46/0.67         <= (~
% 0.46/0.67             ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))))),
% 0.46/0.67      inference('split', [status(esa)], ['0'])).
% 0.46/0.67  thf('2', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(redefinition_k8_relset_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.67       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.46/0.67  thf('3', plain,
% 0.46/0.67      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.46/0.67         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.46/0.67          | ((k8_relset_1 @ X14 @ X15 @ X13 @ X16) = (k10_relat_1 @ X13 @ X16)))),
% 0.46/0.67      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.46/0.67  thf('4', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         ((k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)
% 0.46/0.67           = (k10_relat_1 @ sk_D_1 @ X0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.67  thf('5', plain,
% 0.46/0.67      ((~ (r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ sk_C)))
% 0.46/0.67         <= (~
% 0.46/0.67             ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))))),
% 0.46/0.67      inference('demod', [status(thm)], ['1', '4'])).
% 0.46/0.67  thf('6', plain,
% 0.46/0.67      (~ ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))) | 
% 0.46/0.67       ~ ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_E) @ sk_C)) | 
% 0.46/0.67       ~ ((r2_hidden @ sk_E @ sk_A))),
% 0.46/0.67      inference('split', [status(esa)], ['0'])).
% 0.46/0.67  thf('7', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         ((k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)
% 0.46/0.67           = (k10_relat_1 @ sk_D_1 @ X0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.67  thf('8', plain,
% 0.46/0.67      (((r2_hidden @ sk_E @ sk_A)
% 0.46/0.67        | (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('9', plain,
% 0.46/0.67      (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C)))
% 0.46/0.67         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))))),
% 0.46/0.67      inference('split', [status(esa)], ['8'])).
% 0.46/0.67  thf('10', plain,
% 0.46/0.67      (((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ sk_C)))
% 0.46/0.67         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))))),
% 0.46/0.67      inference('sup+', [status(thm)], ['7', '9'])).
% 0.46/0.67  thf(d13_funct_1, axiom,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.67       ( ![B:$i,C:$i]:
% 0.46/0.67         ( ( ( C ) = ( k10_relat_1 @ A @ B ) ) <=>
% 0.46/0.67           ( ![D:$i]:
% 0.46/0.67             ( ( r2_hidden @ D @ C ) <=>
% 0.46/0.67               ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.46/0.67                 ( r2_hidden @ ( k1_funct_1 @ A @ D ) @ B ) ) ) ) ) ) ))).
% 0.46/0.67  thf('11', plain,
% 0.46/0.67      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.67         (((X7) != (k10_relat_1 @ X6 @ X5))
% 0.46/0.67          | (r2_hidden @ X8 @ (k1_relat_1 @ X6))
% 0.46/0.67          | ~ (r2_hidden @ X8 @ X7)
% 0.46/0.67          | ~ (v1_funct_1 @ X6)
% 0.46/0.67          | ~ (v1_relat_1 @ X6))),
% 0.46/0.67      inference('cnf', [status(esa)], [d13_funct_1])).
% 0.46/0.67  thf('12', plain,
% 0.46/0.67      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.46/0.67         (~ (v1_relat_1 @ X6)
% 0.46/0.67          | ~ (v1_funct_1 @ X6)
% 0.46/0.67          | ~ (r2_hidden @ X8 @ (k10_relat_1 @ X6 @ X5))
% 0.46/0.67          | (r2_hidden @ X8 @ (k1_relat_1 @ X6)))),
% 0.46/0.67      inference('simplify', [status(thm)], ['11'])).
% 0.46/0.67  thf('13', plain,
% 0.46/0.67      ((((r2_hidden @ sk_E @ (k1_relat_1 @ sk_D_1))
% 0.46/0.67         | ~ (v1_funct_1 @ sk_D_1)
% 0.46/0.67         | ~ (v1_relat_1 @ sk_D_1)))
% 0.46/0.67         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))))),
% 0.46/0.67      inference('sup-', [status(thm)], ['10', '12'])).
% 0.46/0.67  thf('14', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(d1_funct_2, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.67       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.67           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.46/0.67             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.46/0.67         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.67           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.46/0.67             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.46/0.67  thf(zf_stmt_1, axiom,
% 0.46/0.67    (![C:$i,B:$i,A:$i]:
% 0.46/0.67     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.46/0.67       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.46/0.67  thf('15', plain,
% 0.46/0.67      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.67         (~ (v1_funct_2 @ X21 @ X19 @ X20)
% 0.46/0.67          | ((X19) = (k1_relset_1 @ X19 @ X20 @ X21))
% 0.46/0.67          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.67  thf('16', plain,
% 0.46/0.67      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)
% 0.46/0.67        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_1)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['14', '15'])).
% 0.46/0.67  thf(zf_stmt_2, axiom,
% 0.46/0.67    (![B:$i,A:$i]:
% 0.46/0.67     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.67       ( zip_tseitin_0 @ B @ A ) ))).
% 0.46/0.67  thf('17', plain,
% 0.46/0.67      (![X17 : $i, X18 : $i]:
% 0.46/0.67         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.46/0.67  thf('18', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.46/0.67  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.46/0.67  thf(zf_stmt_5, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.67       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.46/0.67         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.67           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.46/0.67             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.46/0.67  thf('19', plain,
% 0.46/0.67      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.46/0.67         (~ (zip_tseitin_0 @ X22 @ X23)
% 0.46/0.67          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 0.46/0.67          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.46/0.67  thf('20', plain,
% 0.46/0.67      (((zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)
% 0.46/0.67        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.46/0.67      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.67  thf('21', plain,
% 0.46/0.67      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A))),
% 0.46/0.67      inference('sup-', [status(thm)], ['17', '20'])).
% 0.46/0.67  thf('22', plain, (((sk_B) != (k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('23', plain, ((zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)),
% 0.46/0.67      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.46/0.67  thf('24', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(redefinition_k1_relset_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.67       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.46/0.67  thf('25', plain,
% 0.46/0.67      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.67         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 0.46/0.67          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.46/0.67      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.46/0.67  thf('26', plain,
% 0.46/0.67      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.46/0.67      inference('sup-', [status(thm)], ['24', '25'])).
% 0.46/0.67  thf('27', plain, (((sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.46/0.67      inference('demod', [status(thm)], ['16', '23', '26'])).
% 0.46/0.67  thf('28', plain, ((v1_funct_1 @ sk_D_1)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('29', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(cc2_relat_1, axiom,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( v1_relat_1 @ A ) =>
% 0.46/0.67       ( ![B:$i]:
% 0.46/0.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.46/0.67  thf('30', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.46/0.67          | (v1_relat_1 @ X0)
% 0.46/0.67          | ~ (v1_relat_1 @ X1))),
% 0.46/0.67      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.46/0.67  thf('31', plain,
% 0.46/0.67      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D_1))),
% 0.46/0.67      inference('sup-', [status(thm)], ['29', '30'])).
% 0.46/0.67  thf(fc6_relat_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.46/0.67  thf('32', plain,
% 0.46/0.67      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.46/0.67      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.46/0.67  thf('33', plain, ((v1_relat_1 @ sk_D_1)),
% 0.46/0.67      inference('demod', [status(thm)], ['31', '32'])).
% 0.46/0.67  thf('34', plain,
% 0.46/0.67      (((r2_hidden @ sk_E @ sk_A))
% 0.46/0.67         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))))),
% 0.46/0.67      inference('demod', [status(thm)], ['13', '27', '28', '33'])).
% 0.46/0.67  thf('35', plain,
% 0.46/0.67      ((~ (r2_hidden @ sk_E @ sk_A)) <= (~ ((r2_hidden @ sk_E @ sk_A)))),
% 0.46/0.67      inference('split', [status(esa)], ['0'])).
% 0.46/0.67  thf('36', plain,
% 0.46/0.67      (((r2_hidden @ sk_E @ sk_A)) | 
% 0.46/0.67       ~ ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['34', '35'])).
% 0.46/0.67  thf('37', plain,
% 0.46/0.67      (((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ sk_C)))
% 0.46/0.67         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))))),
% 0.46/0.67      inference('sup+', [status(thm)], ['7', '9'])).
% 0.46/0.67  thf('38', plain,
% 0.46/0.67      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.67         (((X7) != (k10_relat_1 @ X6 @ X5))
% 0.46/0.67          | (r2_hidden @ (k1_funct_1 @ X6 @ X8) @ X5)
% 0.46/0.67          | ~ (r2_hidden @ X8 @ X7)
% 0.46/0.67          | ~ (v1_funct_1 @ X6)
% 0.46/0.67          | ~ (v1_relat_1 @ X6))),
% 0.46/0.67      inference('cnf', [status(esa)], [d13_funct_1])).
% 0.46/0.67  thf('39', plain,
% 0.46/0.67      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.46/0.67         (~ (v1_relat_1 @ X6)
% 0.46/0.67          | ~ (v1_funct_1 @ X6)
% 0.46/0.67          | ~ (r2_hidden @ X8 @ (k10_relat_1 @ X6 @ X5))
% 0.46/0.67          | (r2_hidden @ (k1_funct_1 @ X6 @ X8) @ X5))),
% 0.46/0.67      inference('simplify', [status(thm)], ['38'])).
% 0.46/0.67  thf('40', plain,
% 0.46/0.67      ((((r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_E) @ sk_C)
% 0.46/0.67         | ~ (v1_funct_1 @ sk_D_1)
% 0.46/0.67         | ~ (v1_relat_1 @ sk_D_1)))
% 0.46/0.67         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))))),
% 0.46/0.67      inference('sup-', [status(thm)], ['37', '39'])).
% 0.46/0.67  thf('41', plain, ((v1_funct_1 @ sk_D_1)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('42', plain, ((v1_relat_1 @ sk_D_1)),
% 0.46/0.67      inference('demod', [status(thm)], ['31', '32'])).
% 0.46/0.67  thf('43', plain,
% 0.46/0.67      (((r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_E) @ sk_C))
% 0.46/0.67         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))))),
% 0.46/0.67      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.46/0.67  thf('44', plain,
% 0.46/0.67      ((~ (r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_E) @ sk_C))
% 0.46/0.67         <= (~ ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_E) @ sk_C)))),
% 0.46/0.67      inference('split', [status(esa)], ['0'])).
% 0.46/0.67  thf('45', plain,
% 0.46/0.67      (((r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_E) @ sk_C)) | 
% 0.46/0.67       ~ ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['43', '44'])).
% 0.46/0.67  thf('46', plain,
% 0.46/0.67      (~ ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C)))),
% 0.46/0.67      inference('sat_resolution*', [status(thm)], ['6', '36', '45'])).
% 0.46/0.67  thf('47', plain, (~ (r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ sk_C))),
% 0.46/0.67      inference('simpl_trail', [status(thm)], ['5', '46'])).
% 0.46/0.67  thf('48', plain,
% 0.46/0.67      (((r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_E) @ sk_C)
% 0.46/0.67        | (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('49', plain,
% 0.46/0.67      (((r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_E) @ sk_C))
% 0.46/0.67         <= (((r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_E) @ sk_C)))),
% 0.46/0.67      inference('split', [status(esa)], ['48'])).
% 0.46/0.67  thf('50', plain,
% 0.46/0.67      (((r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_E) @ sk_C)) | 
% 0.46/0.67       ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C)))),
% 0.46/0.67      inference('split', [status(esa)], ['48'])).
% 0.46/0.67  thf('51', plain, (((r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_E) @ sk_C))),
% 0.46/0.67      inference('sat_resolution*', [status(thm)], ['6', '36', '45', '50'])).
% 0.46/0.67  thf('52', plain, ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_E) @ sk_C)),
% 0.46/0.67      inference('simpl_trail', [status(thm)], ['49', '51'])).
% 0.46/0.67  thf('53', plain, (((sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.46/0.67      inference('demod', [status(thm)], ['16', '23', '26'])).
% 0.46/0.67  thf('54', plain,
% 0.46/0.67      (![X5 : $i, X6 : $i, X7 : $i, X9 : $i]:
% 0.46/0.67         (((X7) != (k10_relat_1 @ X6 @ X5))
% 0.46/0.67          | (r2_hidden @ X9 @ X7)
% 0.46/0.67          | ~ (r2_hidden @ (k1_funct_1 @ X6 @ X9) @ X5)
% 0.46/0.67          | ~ (r2_hidden @ X9 @ (k1_relat_1 @ X6))
% 0.46/0.67          | ~ (v1_funct_1 @ X6)
% 0.46/0.67          | ~ (v1_relat_1 @ X6))),
% 0.46/0.67      inference('cnf', [status(esa)], [d13_funct_1])).
% 0.46/0.67  thf('55', plain,
% 0.46/0.67      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.46/0.67         (~ (v1_relat_1 @ X6)
% 0.46/0.67          | ~ (v1_funct_1 @ X6)
% 0.46/0.67          | ~ (r2_hidden @ X9 @ (k1_relat_1 @ X6))
% 0.46/0.67          | ~ (r2_hidden @ (k1_funct_1 @ X6 @ X9) @ X5)
% 0.46/0.67          | (r2_hidden @ X9 @ (k10_relat_1 @ X6 @ X5)))),
% 0.46/0.67      inference('simplify', [status(thm)], ['54'])).
% 0.46/0.67  thf('56', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         (~ (r2_hidden @ X0 @ sk_A)
% 0.46/0.67          | (r2_hidden @ X0 @ (k10_relat_1 @ sk_D_1 @ X1))
% 0.46/0.67          | ~ (r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ X1)
% 0.46/0.67          | ~ (v1_funct_1 @ sk_D_1)
% 0.46/0.67          | ~ (v1_relat_1 @ sk_D_1))),
% 0.46/0.67      inference('sup-', [status(thm)], ['53', '55'])).
% 0.46/0.67  thf('57', plain, ((v1_funct_1 @ sk_D_1)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('58', plain, ((v1_relat_1 @ sk_D_1)),
% 0.46/0.67      inference('demod', [status(thm)], ['31', '32'])).
% 0.46/0.67  thf('59', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         (~ (r2_hidden @ X0 @ sk_A)
% 0.46/0.67          | (r2_hidden @ X0 @ (k10_relat_1 @ sk_D_1 @ X1))
% 0.46/0.67          | ~ (r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ X1))),
% 0.46/0.67      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.46/0.67  thf('60', plain,
% 0.46/0.67      (((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ sk_C))
% 0.46/0.67        | ~ (r2_hidden @ sk_E @ sk_A))),
% 0.46/0.67      inference('sup-', [status(thm)], ['52', '59'])).
% 0.46/0.67  thf('61', plain,
% 0.46/0.67      (((r2_hidden @ sk_E @ sk_A)) <= (((r2_hidden @ sk_E @ sk_A)))),
% 0.46/0.67      inference('split', [status(esa)], ['8'])).
% 0.46/0.67  thf('62', plain,
% 0.46/0.67      (((r2_hidden @ sk_E @ sk_A)) | 
% 0.46/0.67       ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C)))),
% 0.46/0.67      inference('split', [status(esa)], ['8'])).
% 0.46/0.67  thf('63', plain, (((r2_hidden @ sk_E @ sk_A))),
% 0.46/0.67      inference('sat_resolution*', [status(thm)], ['6', '36', '45', '62'])).
% 0.46/0.67  thf('64', plain, ((r2_hidden @ sk_E @ sk_A)),
% 0.46/0.67      inference('simpl_trail', [status(thm)], ['61', '63'])).
% 0.46/0.67  thf('65', plain, ((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ sk_C))),
% 0.46/0.67      inference('demod', [status(thm)], ['60', '64'])).
% 0.46/0.67  thf('66', plain, ($false), inference('demod', [status(thm)], ['47', '65'])).
% 0.46/0.67  
% 0.46/0.67  % SZS output end Refutation
% 0.46/0.67  
% 0.46/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
