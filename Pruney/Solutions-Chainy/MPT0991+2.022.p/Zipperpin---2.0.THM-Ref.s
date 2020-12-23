%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.URrGPpJUZZ

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:33 EST 2020

% Result     : Theorem 1.93s
% Output     : Refutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 217 expanded)
%              Number of leaves         :   52 (  87 expanded)
%              Depth                    :   20
%              Number of atoms          : 1196 (3469 expanded)
%              Number of equality atoms :   66 ( 126 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(t37_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ~ ( ( B != k1_xboole_0 )
          & ? [D: $i] :
              ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
              & ( v1_funct_2 @ D @ B @ A )
              & ( v1_funct_1 @ D ) )
          & ~ ( v2_funct_1 @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ~ ( ( B != k1_xboole_0 )
            & ? [D: $i] :
                ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
                & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
                & ( v1_funct_2 @ D @ B @ A )
                & ( v1_funct_1 @ D ) )
            & ~ ( v2_funct_1 @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t37_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v5_relat_1 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('6',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('7',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['4','7'])).

thf('9',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
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

thf('10',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('11',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('13',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('14',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('15',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('20',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('21',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['11','18','21'])).

thf('23',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('24',plain,(
    ! [X7: $i] :
      ( ( ( k1_relat_1 @ X7 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X7 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ X1 )
       != X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k2_relat_1 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( zip_tseitin_0 @ ( k1_relat_1 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( ( k2_relat_1 @ sk_C_1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['22','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( ( k2_relat_1 @ sk_C_1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('32',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B_1 )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('36',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('39',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['36','39'])).

thf('41',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['33','40'])).

thf(t144_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ! [B: $i] :
            ~ ( ( r2_hidden @ B @ ( k2_relat_1 @ A ) )
              & ! [C: $i] :
                  ( ( k10_relat_1 @ A @ ( k1_tarski @ B ) )
                 != ( k1_tarski @ C ) ) )
      <=> ( v2_funct_1 @ A ) ) ) )).

thf('42',plain,(
    ! [X8: $i] :
      ( ( r2_hidden @ ( sk_B @ X8 ) @ ( k2_relat_1 @ X8 ) )
      | ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t144_funct_1])).

thf('43',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_1 ) @ k1_xboole_0 )
    | ( sk_B_1
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('45',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_1 ) @ k1_xboole_0 )
    | ( sk_B_1
      = ( k1_relat_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('47',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('48',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('49',plain,(
    ! [X3: $i,X4: $i] :
      ~ ( r2_hidden @ X3 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('50',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( v2_funct_1 @ sk_C_1 )
    | ( sk_B_1
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(clc,[status(thm)],['46','50'])).

thf('52',plain,(
    ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( sk_B_1
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['51','52'])).

thf(t47_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
              & ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) )
           => ( v2_funct_1 @ B ) ) ) ) )).

thf('54',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( v2_funct_1 @ X11 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X11 ) @ ( k1_relat_1 @ X12 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t47_funct_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X0 @ sk_D ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('58',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ sk_B_1 )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X0 @ sk_D ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['55','58','59'])).

thf('61',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( v2_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('63',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v2_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('69',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ( ( k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46 )
        = ( k5_relat_1 @ X43 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C_1 @ X0 )
        = ( k5_relat_1 @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C_1 @ X0 )
        = ( k5_relat_1 @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
      = ( k5_relat_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['67','72'])).

thf('74',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('76',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('77',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('80',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['78','83'])).

thf('85',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('87',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( X23 = X26 )
      | ~ ( r2_relset_1 @ X24 @ X25 @ X23 @ X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','88'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('90',plain,(
    ! [X42: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('91',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('92',plain,(
    ! [X42: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X42 ) ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['89','92'])).

thf('94',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['73','74','93'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('95',plain,(
    ! [X13: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('96',plain,(
    $false ),
    inference(demod,[status(thm)],['66','94','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.URrGPpJUZZ
% 0.15/0.34  % Computer   : n003.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 19:58:12 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 1.93/2.17  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.93/2.17  % Solved by: fo/fo7.sh
% 1.93/2.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.93/2.17  % done 1387 iterations in 1.698s
% 1.93/2.17  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.93/2.17  % SZS output start Refutation
% 1.93/2.17  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.93/2.17  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.93/2.17  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.93/2.17  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.93/2.17  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.93/2.17  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.93/2.17  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.93/2.17  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.93/2.17  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.93/2.17  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.93/2.17  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.93/2.17  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.93/2.17  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.93/2.17  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.93/2.17  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.93/2.17  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.93/2.17  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.93/2.17  thf(sk_A_type, type, sk_A: $i).
% 1.93/2.17  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.93/2.17  thf(sk_B_type, type, sk_B: $i > $i).
% 1.93/2.17  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.93/2.17  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.93/2.17  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.93/2.17  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.93/2.17  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.93/2.17  thf(sk_D_type, type, sk_D: $i).
% 1.93/2.17  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.93/2.17  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.93/2.17  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.93/2.17  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.93/2.17  thf(t37_funct_2, conjecture,
% 1.93/2.17    (![A:$i,B:$i,C:$i]:
% 1.93/2.17     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.93/2.17         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.93/2.17       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.93/2.17            ( ?[D:$i]:
% 1.93/2.17              ( ( r2_relset_1 @
% 1.93/2.17                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.93/2.17                  ( k6_partfun1 @ A ) ) & 
% 1.93/2.17                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) & 
% 1.93/2.17                ( v1_funct_2 @ D @ B @ A ) & ( v1_funct_1 @ D ) ) ) & 
% 1.93/2.17            ( ~( v2_funct_1 @ C ) ) ) ) ))).
% 1.93/2.17  thf(zf_stmt_0, negated_conjecture,
% 1.93/2.17    (~( ![A:$i,B:$i,C:$i]:
% 1.93/2.17        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.93/2.17            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.93/2.17          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.93/2.17               ( ?[D:$i]:
% 1.93/2.17                 ( ( r2_relset_1 @
% 1.93/2.17                     A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.93/2.17                     ( k6_partfun1 @ A ) ) & 
% 1.93/2.17                   ( m1_subset_1 @
% 1.93/2.17                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) & 
% 1.93/2.17                   ( v1_funct_2 @ D @ B @ A ) & ( v1_funct_1 @ D ) ) ) & 
% 1.93/2.17               ( ~( v2_funct_1 @ C ) ) ) ) ) )),
% 1.93/2.17    inference('cnf.neg', [status(esa)], [t37_funct_2])).
% 1.93/2.17  thf('0', plain,
% 1.93/2.17      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.93/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.17  thf(cc2_relset_1, axiom,
% 1.93/2.17    (![A:$i,B:$i,C:$i]:
% 1.93/2.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.93/2.17       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.93/2.17  thf('1', plain,
% 1.93/2.17      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.93/2.17         ((v5_relat_1 @ X17 @ X19)
% 1.93/2.17          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.93/2.17      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.93/2.17  thf('2', plain, ((v5_relat_1 @ sk_C_1 @ sk_B_1)),
% 1.93/2.17      inference('sup-', [status(thm)], ['0', '1'])).
% 1.93/2.17  thf(d19_relat_1, axiom,
% 1.93/2.17    (![A:$i,B:$i]:
% 1.93/2.17     ( ( v1_relat_1 @ B ) =>
% 1.93/2.17       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.93/2.17  thf('3', plain,
% 1.93/2.17      (![X5 : $i, X6 : $i]:
% 1.93/2.17         (~ (v5_relat_1 @ X5 @ X6)
% 1.93/2.17          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 1.93/2.17          | ~ (v1_relat_1 @ X5))),
% 1.93/2.17      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.93/2.17  thf('4', plain,
% 1.93/2.17      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))),
% 1.93/2.17      inference('sup-', [status(thm)], ['2', '3'])).
% 1.93/2.17  thf('5', plain,
% 1.93/2.17      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.93/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.17  thf(cc1_relset_1, axiom,
% 1.93/2.17    (![A:$i,B:$i,C:$i]:
% 1.93/2.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.93/2.17       ( v1_relat_1 @ C ) ))).
% 1.93/2.17  thf('6', plain,
% 1.93/2.17      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.93/2.17         ((v1_relat_1 @ X14)
% 1.93/2.17          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.93/2.17      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.93/2.17  thf('7', plain, ((v1_relat_1 @ sk_C_1)),
% 1.93/2.17      inference('sup-', [status(thm)], ['5', '6'])).
% 1.93/2.17  thf('8', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)),
% 1.93/2.17      inference('demod', [status(thm)], ['4', '7'])).
% 1.93/2.17  thf('9', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 1.93/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.17  thf(d1_funct_2, axiom,
% 1.93/2.17    (![A:$i,B:$i,C:$i]:
% 1.93/2.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.93/2.17       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.93/2.17           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.93/2.17             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.93/2.17         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.93/2.17           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.93/2.17             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.93/2.17  thf(zf_stmt_1, axiom,
% 1.93/2.17    (![C:$i,B:$i,A:$i]:
% 1.93/2.17     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.93/2.17       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.93/2.17  thf('10', plain,
% 1.93/2.17      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.93/2.17         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 1.93/2.17          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 1.93/2.17          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 1.93/2.17      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.93/2.17  thf('11', plain,
% 1.93/2.17      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 1.93/2.17        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 1.93/2.17      inference('sup-', [status(thm)], ['9', '10'])).
% 1.93/2.17  thf(zf_stmt_2, axiom,
% 1.93/2.17    (![B:$i,A:$i]:
% 1.93/2.17     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.93/2.17       ( zip_tseitin_0 @ B @ A ) ))).
% 1.93/2.17  thf('12', plain,
% 1.93/2.17      (![X27 : $i, X28 : $i]:
% 1.93/2.17         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 1.93/2.17      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.93/2.17  thf('13', plain,
% 1.93/2.17      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.93/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.17  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.93/2.17  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.93/2.17  thf(zf_stmt_5, axiom,
% 1.93/2.17    (![A:$i,B:$i,C:$i]:
% 1.93/2.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.93/2.17       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.93/2.17         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.93/2.17           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.93/2.17             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.93/2.17  thf('14', plain,
% 1.93/2.17      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.93/2.17         (~ (zip_tseitin_0 @ X32 @ X33)
% 1.93/2.17          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 1.93/2.17          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 1.93/2.17      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.93/2.17  thf('15', plain,
% 1.93/2.17      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 1.93/2.17        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 1.93/2.17      inference('sup-', [status(thm)], ['13', '14'])).
% 1.93/2.17  thf('16', plain,
% 1.93/2.17      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A))),
% 1.93/2.17      inference('sup-', [status(thm)], ['12', '15'])).
% 1.93/2.17  thf('17', plain, (((sk_B_1) != (k1_xboole_0))),
% 1.93/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.17  thf('18', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)),
% 1.93/2.17      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 1.93/2.17  thf('19', plain,
% 1.93/2.17      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.93/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.17  thf(redefinition_k1_relset_1, axiom,
% 1.93/2.17    (![A:$i,B:$i,C:$i]:
% 1.93/2.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.93/2.17       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.93/2.17  thf('20', plain,
% 1.93/2.17      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.93/2.17         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 1.93/2.17          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.93/2.17      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.93/2.17  thf('21', plain,
% 1.93/2.17      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 1.93/2.17      inference('sup-', [status(thm)], ['19', '20'])).
% 1.93/2.17  thf('22', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 1.93/2.17      inference('demod', [status(thm)], ['11', '18', '21'])).
% 1.93/2.17  thf('23', plain,
% 1.93/2.17      (![X27 : $i, X28 : $i]:
% 1.93/2.17         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 1.93/2.17      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.93/2.17  thf(t65_relat_1, axiom,
% 1.93/2.17    (![A:$i]:
% 1.93/2.17     ( ( v1_relat_1 @ A ) =>
% 1.93/2.17       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 1.93/2.17         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 1.93/2.17  thf('24', plain,
% 1.93/2.17      (![X7 : $i]:
% 1.93/2.17         (((k1_relat_1 @ X7) != (k1_xboole_0))
% 1.93/2.17          | ((k2_relat_1 @ X7) = (k1_xboole_0))
% 1.93/2.17          | ~ (v1_relat_1 @ X7))),
% 1.93/2.17      inference('cnf', [status(esa)], [t65_relat_1])).
% 1.93/2.17  thf('25', plain,
% 1.93/2.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.93/2.17         (((k1_relat_1 @ X1) != (X0))
% 1.93/2.17          | (zip_tseitin_0 @ X0 @ X2)
% 1.93/2.17          | ~ (v1_relat_1 @ X1)
% 1.93/2.17          | ((k2_relat_1 @ X1) = (k1_xboole_0)))),
% 1.93/2.17      inference('sup-', [status(thm)], ['23', '24'])).
% 1.93/2.17  thf('26', plain,
% 1.93/2.17      (![X1 : $i, X2 : $i]:
% 1.93/2.17         (((k2_relat_1 @ X1) = (k1_xboole_0))
% 1.93/2.17          | ~ (v1_relat_1 @ X1)
% 1.93/2.17          | (zip_tseitin_0 @ (k1_relat_1 @ X1) @ X2))),
% 1.93/2.17      inference('simplify', [status(thm)], ['25'])).
% 1.93/2.17  thf('27', plain,
% 1.93/2.17      (![X0 : $i]:
% 1.93/2.17         ((zip_tseitin_0 @ sk_A @ X0)
% 1.93/2.17          | ~ (v1_relat_1 @ sk_C_1)
% 1.93/2.17          | ((k2_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 1.93/2.17      inference('sup+', [status(thm)], ['22', '26'])).
% 1.93/2.17  thf('28', plain, ((v1_relat_1 @ sk_C_1)),
% 1.93/2.17      inference('sup-', [status(thm)], ['5', '6'])).
% 1.93/2.17  thf('29', plain,
% 1.93/2.17      (![X0 : $i]:
% 1.93/2.17         ((zip_tseitin_0 @ sk_A @ X0) | ((k2_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 1.93/2.17      inference('demod', [status(thm)], ['27', '28'])).
% 1.93/2.17  thf('30', plain,
% 1.93/2.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 1.93/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.17  thf('31', plain,
% 1.93/2.17      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.93/2.17         (~ (zip_tseitin_0 @ X32 @ X33)
% 1.93/2.17          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 1.93/2.17          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 1.93/2.17      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.93/2.17  thf('32', plain,
% 1.93/2.17      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B_1)
% 1.93/2.17        | ~ (zip_tseitin_0 @ sk_A @ sk_B_1))),
% 1.93/2.17      inference('sup-', [status(thm)], ['30', '31'])).
% 1.93/2.17  thf('33', plain,
% 1.93/2.17      ((((k2_relat_1 @ sk_C_1) = (k1_xboole_0))
% 1.93/2.17        | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B_1))),
% 1.93/2.17      inference('sup-', [status(thm)], ['29', '32'])).
% 1.93/2.17  thf('34', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 1.93/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.17  thf('35', plain,
% 1.93/2.17      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.93/2.17         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 1.93/2.17          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 1.93/2.17          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 1.93/2.17      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.93/2.17  thf('36', plain,
% 1.93/2.17      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B_1)
% 1.93/2.17        | ((sk_B_1) = (k1_relset_1 @ sk_B_1 @ sk_A @ sk_D)))),
% 1.93/2.17      inference('sup-', [status(thm)], ['34', '35'])).
% 1.93/2.17  thf('37', plain,
% 1.93/2.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 1.93/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.17  thf('38', plain,
% 1.93/2.17      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.93/2.17         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 1.93/2.17          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.93/2.17      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.93/2.17  thf('39', plain,
% 1.93/2.17      (((k1_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.93/2.17      inference('sup-', [status(thm)], ['37', '38'])).
% 1.93/2.17  thf('40', plain,
% 1.93/2.17      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B_1)
% 1.93/2.17        | ((sk_B_1) = (k1_relat_1 @ sk_D)))),
% 1.93/2.17      inference('demod', [status(thm)], ['36', '39'])).
% 1.93/2.17  thf('41', plain,
% 1.93/2.17      ((((k2_relat_1 @ sk_C_1) = (k1_xboole_0))
% 1.93/2.17        | ((sk_B_1) = (k1_relat_1 @ sk_D)))),
% 1.93/2.17      inference('sup-', [status(thm)], ['33', '40'])).
% 1.93/2.17  thf(t144_funct_1, axiom,
% 1.93/2.17    (![A:$i]:
% 1.93/2.17     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.93/2.17       ( ( ![B:$i]:
% 1.93/2.17           ( ~( ( r2_hidden @ B @ ( k2_relat_1 @ A ) ) & 
% 1.93/2.17                ( ![C:$i]:
% 1.93/2.17                  ( ( k10_relat_1 @ A @ ( k1_tarski @ B ) ) !=
% 1.93/2.17                    ( k1_tarski @ C ) ) ) ) ) ) <=>
% 1.93/2.17         ( v2_funct_1 @ A ) ) ))).
% 1.93/2.17  thf('42', plain,
% 1.93/2.17      (![X8 : $i]:
% 1.93/2.17         ((r2_hidden @ (sk_B @ X8) @ (k2_relat_1 @ X8))
% 1.93/2.17          | (v2_funct_1 @ X8)
% 1.93/2.17          | ~ (v1_funct_1 @ X8)
% 1.93/2.17          | ~ (v1_relat_1 @ X8))),
% 1.93/2.17      inference('cnf', [status(esa)], [t144_funct_1])).
% 1.93/2.17  thf('43', plain,
% 1.93/2.17      (((r2_hidden @ (sk_B @ sk_C_1) @ k1_xboole_0)
% 1.93/2.17        | ((sk_B_1) = (k1_relat_1 @ sk_D))
% 1.93/2.17        | ~ (v1_relat_1 @ sk_C_1)
% 1.93/2.17        | ~ (v1_funct_1 @ sk_C_1)
% 1.93/2.17        | (v2_funct_1 @ sk_C_1))),
% 1.93/2.17      inference('sup+', [status(thm)], ['41', '42'])).
% 1.93/2.17  thf('44', plain, ((v1_relat_1 @ sk_C_1)),
% 1.93/2.17      inference('sup-', [status(thm)], ['5', '6'])).
% 1.93/2.17  thf('45', plain, ((v1_funct_1 @ sk_C_1)),
% 1.93/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.17  thf('46', plain,
% 1.93/2.17      (((r2_hidden @ (sk_B @ sk_C_1) @ k1_xboole_0)
% 1.93/2.17        | ((sk_B_1) = (k1_relat_1 @ sk_D))
% 1.93/2.17        | (v2_funct_1 @ sk_C_1))),
% 1.93/2.17      inference('demod', [status(thm)], ['43', '44', '45'])).
% 1.93/2.17  thf(t113_zfmisc_1, axiom,
% 1.93/2.17    (![A:$i,B:$i]:
% 1.93/2.17     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.93/2.17       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.93/2.17  thf('47', plain,
% 1.93/2.17      (![X1 : $i, X2 : $i]:
% 1.93/2.17         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 1.93/2.17      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.93/2.17  thf('48', plain,
% 1.93/2.17      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.93/2.17      inference('simplify', [status(thm)], ['47'])).
% 1.93/2.17  thf(t152_zfmisc_1, axiom,
% 1.93/2.17    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 1.93/2.17  thf('49', plain,
% 1.93/2.17      (![X3 : $i, X4 : $i]: ~ (r2_hidden @ X3 @ (k2_zfmisc_1 @ X3 @ X4))),
% 1.93/2.17      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 1.93/2.17  thf('50', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.93/2.17      inference('sup-', [status(thm)], ['48', '49'])).
% 1.93/2.17  thf('51', plain,
% 1.93/2.17      (((v2_funct_1 @ sk_C_1) | ((sk_B_1) = (k1_relat_1 @ sk_D)))),
% 1.93/2.17      inference('clc', [status(thm)], ['46', '50'])).
% 1.93/2.17  thf('52', plain, (~ (v2_funct_1 @ sk_C_1)),
% 1.93/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.17  thf('53', plain, (((sk_B_1) = (k1_relat_1 @ sk_D))),
% 1.93/2.17      inference('clc', [status(thm)], ['51', '52'])).
% 1.93/2.17  thf(t47_funct_1, axiom,
% 1.93/2.17    (![A:$i]:
% 1.93/2.17     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.93/2.17       ( ![B:$i]:
% 1.93/2.17         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.93/2.17           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 1.93/2.17               ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) =>
% 1.93/2.17             ( v2_funct_1 @ B ) ) ) ) ))).
% 1.93/2.17  thf('54', plain,
% 1.93/2.17      (![X11 : $i, X12 : $i]:
% 1.93/2.17         (~ (v1_relat_1 @ X11)
% 1.93/2.17          | ~ (v1_funct_1 @ X11)
% 1.93/2.17          | (v2_funct_1 @ X11)
% 1.93/2.17          | ~ (r1_tarski @ (k2_relat_1 @ X11) @ (k1_relat_1 @ X12))
% 1.93/2.17          | ~ (v2_funct_1 @ (k5_relat_1 @ X11 @ X12))
% 1.93/2.17          | ~ (v1_funct_1 @ X12)
% 1.93/2.17          | ~ (v1_relat_1 @ X12))),
% 1.93/2.17      inference('cnf', [status(esa)], [t47_funct_1])).
% 1.93/2.17  thf('55', plain,
% 1.93/2.17      (![X0 : $i]:
% 1.93/2.17         (~ (r1_tarski @ (k2_relat_1 @ X0) @ sk_B_1)
% 1.93/2.17          | ~ (v1_relat_1 @ sk_D)
% 1.93/2.17          | ~ (v1_funct_1 @ sk_D)
% 1.93/2.17          | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ sk_D))
% 1.93/2.17          | (v2_funct_1 @ X0)
% 1.93/2.17          | ~ (v1_funct_1 @ X0)
% 1.93/2.17          | ~ (v1_relat_1 @ X0))),
% 1.93/2.17      inference('sup-', [status(thm)], ['53', '54'])).
% 1.93/2.17  thf('56', plain,
% 1.93/2.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 1.93/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.17  thf('57', plain,
% 1.93/2.17      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.93/2.17         ((v1_relat_1 @ X14)
% 1.93/2.17          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.93/2.17      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.93/2.17  thf('58', plain, ((v1_relat_1 @ sk_D)),
% 1.93/2.17      inference('sup-', [status(thm)], ['56', '57'])).
% 1.93/2.17  thf('59', plain, ((v1_funct_1 @ sk_D)),
% 1.93/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.17  thf('60', plain,
% 1.93/2.17      (![X0 : $i]:
% 1.93/2.17         (~ (r1_tarski @ (k2_relat_1 @ X0) @ sk_B_1)
% 1.93/2.17          | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ sk_D))
% 1.93/2.17          | (v2_funct_1 @ X0)
% 1.93/2.17          | ~ (v1_funct_1 @ X0)
% 1.93/2.17          | ~ (v1_relat_1 @ X0))),
% 1.93/2.17      inference('demod', [status(thm)], ['55', '58', '59'])).
% 1.93/2.17  thf('61', plain,
% 1.93/2.17      ((~ (v1_relat_1 @ sk_C_1)
% 1.93/2.17        | ~ (v1_funct_1 @ sk_C_1)
% 1.93/2.17        | (v2_funct_1 @ sk_C_1)
% 1.93/2.17        | ~ (v2_funct_1 @ (k5_relat_1 @ sk_C_1 @ sk_D)))),
% 1.93/2.17      inference('sup-', [status(thm)], ['8', '60'])).
% 1.93/2.17  thf('62', plain, ((v1_relat_1 @ sk_C_1)),
% 1.93/2.17      inference('sup-', [status(thm)], ['5', '6'])).
% 1.93/2.17  thf('63', plain, ((v1_funct_1 @ sk_C_1)),
% 1.93/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.17  thf('64', plain,
% 1.93/2.17      (((v2_funct_1 @ sk_C_1) | ~ (v2_funct_1 @ (k5_relat_1 @ sk_C_1 @ sk_D)))),
% 1.93/2.17      inference('demod', [status(thm)], ['61', '62', '63'])).
% 1.93/2.17  thf('65', plain, (~ (v2_funct_1 @ sk_C_1)),
% 1.93/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.17  thf('66', plain, (~ (v2_funct_1 @ (k5_relat_1 @ sk_C_1 @ sk_D))),
% 1.93/2.17      inference('clc', [status(thm)], ['64', '65'])).
% 1.93/2.17  thf('67', plain,
% 1.93/2.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 1.93/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.17  thf('68', plain,
% 1.93/2.17      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.93/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.17  thf(redefinition_k1_partfun1, axiom,
% 1.93/2.17    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.93/2.17     ( ( ( v1_funct_1 @ E ) & 
% 1.93/2.17         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.93/2.17         ( v1_funct_1 @ F ) & 
% 1.93/2.17         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.93/2.17       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.93/2.17  thf('69', plain,
% 1.93/2.17      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 1.93/2.17         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 1.93/2.17          | ~ (v1_funct_1 @ X43)
% 1.93/2.17          | ~ (v1_funct_1 @ X46)
% 1.93/2.17          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 1.93/2.17          | ((k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46)
% 1.93/2.17              = (k5_relat_1 @ X43 @ X46)))),
% 1.93/2.17      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.93/2.17  thf('70', plain,
% 1.93/2.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.93/2.17         (((k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C_1 @ X0)
% 1.93/2.17            = (k5_relat_1 @ sk_C_1 @ X0))
% 1.93/2.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.93/2.17          | ~ (v1_funct_1 @ X0)
% 1.93/2.17          | ~ (v1_funct_1 @ sk_C_1))),
% 1.93/2.17      inference('sup-', [status(thm)], ['68', '69'])).
% 1.93/2.17  thf('71', plain, ((v1_funct_1 @ sk_C_1)),
% 1.93/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.17  thf('72', plain,
% 1.93/2.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.93/2.17         (((k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C_1 @ X0)
% 1.93/2.17            = (k5_relat_1 @ sk_C_1 @ X0))
% 1.93/2.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.93/2.17          | ~ (v1_funct_1 @ X0))),
% 1.93/2.17      inference('demod', [status(thm)], ['70', '71'])).
% 1.93/2.17  thf('73', plain,
% 1.93/2.17      ((~ (v1_funct_1 @ sk_D)
% 1.93/2.17        | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 1.93/2.17            = (k5_relat_1 @ sk_C_1 @ sk_D)))),
% 1.93/2.17      inference('sup-', [status(thm)], ['67', '72'])).
% 1.93/2.17  thf('74', plain, ((v1_funct_1 @ sk_D)),
% 1.93/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.17  thf('75', plain,
% 1.93/2.17      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.93/2.17        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ 
% 1.93/2.17        (k6_partfun1 @ sk_A))),
% 1.93/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.17  thf(redefinition_k6_partfun1, axiom,
% 1.93/2.17    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.93/2.17  thf('76', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 1.93/2.17      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.93/2.17  thf('77', plain,
% 1.93/2.17      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.93/2.17        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ 
% 1.93/2.17        (k6_relat_1 @ sk_A))),
% 1.93/2.17      inference('demod', [status(thm)], ['75', '76'])).
% 1.93/2.17  thf('78', plain,
% 1.93/2.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 1.93/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.17  thf('79', plain,
% 1.93/2.17      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.93/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.17  thf(dt_k1_partfun1, axiom,
% 1.93/2.17    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.93/2.17     ( ( ( v1_funct_1 @ E ) & 
% 1.93/2.17         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.93/2.17         ( v1_funct_1 @ F ) & 
% 1.93/2.17         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.93/2.17       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.93/2.17         ( m1_subset_1 @
% 1.93/2.17           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.93/2.17           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.93/2.17  thf('80', plain,
% 1.93/2.17      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.93/2.17         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 1.93/2.17          | ~ (v1_funct_1 @ X35)
% 1.93/2.17          | ~ (v1_funct_1 @ X38)
% 1.93/2.17          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 1.93/2.17          | (m1_subset_1 @ (k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38) @ 
% 1.93/2.17             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X40))))),
% 1.93/2.17      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.93/2.17  thf('81', plain,
% 1.93/2.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.93/2.17         ((m1_subset_1 @ 
% 1.93/2.17           (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 1.93/2.17           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.93/2.17          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.93/2.17          | ~ (v1_funct_1 @ X1)
% 1.93/2.17          | ~ (v1_funct_1 @ sk_C_1))),
% 1.93/2.17      inference('sup-', [status(thm)], ['79', '80'])).
% 1.93/2.17  thf('82', plain, ((v1_funct_1 @ sk_C_1)),
% 1.93/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.17  thf('83', plain,
% 1.93/2.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.93/2.17         ((m1_subset_1 @ 
% 1.93/2.17           (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 1.93/2.17           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.93/2.17          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.93/2.17          | ~ (v1_funct_1 @ X1))),
% 1.93/2.17      inference('demod', [status(thm)], ['81', '82'])).
% 1.93/2.17  thf('84', plain,
% 1.93/2.17      ((~ (v1_funct_1 @ sk_D)
% 1.93/2.17        | (m1_subset_1 @ 
% 1.93/2.17           (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ 
% 1.93/2.17           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.93/2.17      inference('sup-', [status(thm)], ['78', '83'])).
% 1.93/2.17  thf('85', plain, ((v1_funct_1 @ sk_D)),
% 1.93/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.17  thf('86', plain,
% 1.93/2.17      ((m1_subset_1 @ 
% 1.93/2.17        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ 
% 1.93/2.17        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.93/2.17      inference('demod', [status(thm)], ['84', '85'])).
% 1.93/2.17  thf(redefinition_r2_relset_1, axiom,
% 1.93/2.17    (![A:$i,B:$i,C:$i,D:$i]:
% 1.93/2.17     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.93/2.17         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.93/2.17       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.93/2.17  thf('87', plain,
% 1.93/2.17      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.93/2.17         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 1.93/2.17          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 1.93/2.17          | ((X23) = (X26))
% 1.93/2.17          | ~ (r2_relset_1 @ X24 @ X25 @ X23 @ X26))),
% 1.93/2.17      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.93/2.17  thf('88', plain,
% 1.93/2.17      (![X0 : $i]:
% 1.93/2.17         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.93/2.17             (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ X0)
% 1.93/2.17          | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 1.93/2.17              = (X0))
% 1.93/2.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.93/2.17      inference('sup-', [status(thm)], ['86', '87'])).
% 1.93/2.17  thf('89', plain,
% 1.93/2.17      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 1.93/2.17           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.93/2.17        | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 1.93/2.17            = (k6_relat_1 @ sk_A)))),
% 1.93/2.17      inference('sup-', [status(thm)], ['77', '88'])).
% 1.93/2.17  thf(dt_k6_partfun1, axiom,
% 1.93/2.17    (![A:$i]:
% 1.93/2.17     ( ( m1_subset_1 @
% 1.93/2.17         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 1.93/2.17       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 1.93/2.17  thf('90', plain,
% 1.93/2.17      (![X42 : $i]:
% 1.93/2.17         (m1_subset_1 @ (k6_partfun1 @ X42) @ 
% 1.93/2.17          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X42)))),
% 1.93/2.17      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.93/2.17  thf('91', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 1.93/2.17      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.93/2.17  thf('92', plain,
% 1.93/2.17      (![X42 : $i]:
% 1.93/2.17         (m1_subset_1 @ (k6_relat_1 @ X42) @ 
% 1.93/2.17          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X42)))),
% 1.93/2.17      inference('demod', [status(thm)], ['90', '91'])).
% 1.93/2.17  thf('93', plain,
% 1.93/2.17      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 1.93/2.17         = (k6_relat_1 @ sk_A))),
% 1.93/2.17      inference('demod', [status(thm)], ['89', '92'])).
% 1.93/2.17  thf('94', plain, (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_C_1 @ sk_D))),
% 1.93/2.17      inference('demod', [status(thm)], ['73', '74', '93'])).
% 1.93/2.17  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 1.93/2.17  thf('95', plain, (![X13 : $i]: (v2_funct_1 @ (k6_relat_1 @ X13))),
% 1.93/2.17      inference('cnf', [status(esa)], [t52_funct_1])).
% 1.93/2.17  thf('96', plain, ($false),
% 1.93/2.17      inference('demod', [status(thm)], ['66', '94', '95'])).
% 1.93/2.17  
% 1.93/2.17  % SZS output end Refutation
% 1.93/2.17  
% 1.93/2.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
