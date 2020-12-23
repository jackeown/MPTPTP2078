%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dPPvsMBRs3

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:32 EST 2020

% Result     : Theorem 2.23s
% Output     : Refutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 236 expanded)
%              Number of leaves         :   52 (  92 expanded)
%              Depth                    :   20
%              Number of atoms          : 1203 (3927 expanded)
%              Number of equality atoms :   67 ( 140 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

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

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v5_relat_1 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ( X30
        = ( k1_relset_1 @ X30 @ X31 @ X32 ) )
      | ~ ( zip_tseitin_1 @ X32 @ X31 @ X30 ) ) ),
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
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X28 = k1_xboole_0 ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X34 )
      | ( zip_tseitin_1 @ X35 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
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
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X28 = k1_xboole_0 ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X34 )
      | ( zip_tseitin_1 @ X35 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ( X30
        = ( k1_relset_1 @ X30 @ X31 @ X32 ) )
      | ~ ( zip_tseitin_1 @ X32 @ X31 @ X30 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
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
    ! [X10: $i] :
      ( ( r2_hidden @ ( sk_B @ X10 ) @ ( k2_relat_1 @ X10 ) )
      | ( v2_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( v2_funct_1 @ X13 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X13 ) @ ( k1_relat_1 @ X14 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X13 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
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
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('68',plain,(
    ! [X50: $i] :
      ( ( k6_partfun1 @ X50 )
      = ( k6_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('69',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
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

thf('72',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ( ( k1_partfun1 @ X45 @ X46 @ X48 @ X49 @ X44 @ X47 )
        = ( k5_relat_1 @ X44 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C_1 @ X0 )
        = ( k5_relat_1 @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C_1 @ X0 )
        = ( k5_relat_1 @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
      = ( k5_relat_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['70','75'])).

thf('77',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
    = ( k5_relat_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['69','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
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

thf('82',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['80','85'])).

thf('87',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
    = ( k5_relat_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('89',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('90',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( X24 = X27 )
      | ~ ( r2_relset_1 @ X25 @ X26 @ X24 @ X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C_1 @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C_1 @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','91'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('93',plain,(
    ! [X43: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X43 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('94',plain,(
    ! [X50: $i] :
      ( ( k6_partfun1 @ X50 )
      = ( k6_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('95',plain,(
    ! [X43: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X43 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X43 ) ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k5_relat_1 @ sk_C_1 @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['92','95'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('97',plain,(
    ! [X9: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('98',plain,(
    $false ),
    inference(demod,[status(thm)],['66','96','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dPPvsMBRs3
% 0.15/0.38  % Computer   : n019.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 18:43:37 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.39  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 2.23/2.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.23/2.45  % Solved by: fo/fo7.sh
% 2.23/2.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.23/2.45  % done 1318 iterations in 1.953s
% 2.23/2.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.23/2.45  % SZS output start Refutation
% 2.23/2.45  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.23/2.45  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 2.23/2.45  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.23/2.45  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.23/2.45  thf(sk_B_type, type, sk_B: $i > $i).
% 2.23/2.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.23/2.45  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.23/2.45  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.23/2.45  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.23/2.45  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.23/2.45  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.23/2.45  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.23/2.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.23/2.45  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.23/2.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.23/2.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.23/2.45  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.23/2.45  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.23/2.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.23/2.45  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.23/2.45  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.23/2.45  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.23/2.45  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 2.23/2.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.23/2.45  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.23/2.45  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.23/2.45  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.23/2.45  thf(sk_D_type, type, sk_D: $i).
% 2.23/2.45  thf(sk_A_type, type, sk_A: $i).
% 2.23/2.45  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.23/2.45  thf(t37_funct_2, conjecture,
% 2.23/2.45    (![A:$i,B:$i,C:$i]:
% 2.23/2.45     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.23/2.45         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.23/2.45       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 2.23/2.45            ( ?[D:$i]:
% 2.23/2.45              ( ( r2_relset_1 @
% 2.23/2.45                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.23/2.45                  ( k6_partfun1 @ A ) ) & 
% 2.23/2.45                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) & 
% 2.23/2.45                ( v1_funct_2 @ D @ B @ A ) & ( v1_funct_1 @ D ) ) ) & 
% 2.23/2.45            ( ~( v2_funct_1 @ C ) ) ) ) ))).
% 2.23/2.45  thf(zf_stmt_0, negated_conjecture,
% 2.23/2.45    (~( ![A:$i,B:$i,C:$i]:
% 2.23/2.45        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.23/2.45            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.23/2.45          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 2.23/2.45               ( ?[D:$i]:
% 2.23/2.45                 ( ( r2_relset_1 @
% 2.23/2.45                     A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.23/2.45                     ( k6_partfun1 @ A ) ) & 
% 2.23/2.45                   ( m1_subset_1 @
% 2.23/2.45                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) & 
% 2.23/2.45                   ( v1_funct_2 @ D @ B @ A ) & ( v1_funct_1 @ D ) ) ) & 
% 2.23/2.45               ( ~( v2_funct_1 @ C ) ) ) ) ) )),
% 2.23/2.45    inference('cnf.neg', [status(esa)], [t37_funct_2])).
% 2.23/2.45  thf('0', plain,
% 2.23/2.45      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.23/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.45  thf(cc2_relset_1, axiom,
% 2.23/2.45    (![A:$i,B:$i,C:$i]:
% 2.23/2.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.23/2.45       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.23/2.45  thf('1', plain,
% 2.23/2.45      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.23/2.45         ((v5_relat_1 @ X18 @ X20)
% 2.23/2.45          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 2.23/2.45      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.23/2.45  thf('2', plain, ((v5_relat_1 @ sk_C_1 @ sk_B_1)),
% 2.23/2.45      inference('sup-', [status(thm)], ['0', '1'])).
% 2.23/2.45  thf(d19_relat_1, axiom,
% 2.23/2.45    (![A:$i,B:$i]:
% 2.23/2.45     ( ( v1_relat_1 @ B ) =>
% 2.23/2.45       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 2.23/2.45  thf('3', plain,
% 2.23/2.45      (![X5 : $i, X6 : $i]:
% 2.23/2.45         (~ (v5_relat_1 @ X5 @ X6)
% 2.23/2.45          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 2.23/2.45          | ~ (v1_relat_1 @ X5))),
% 2.23/2.45      inference('cnf', [status(esa)], [d19_relat_1])).
% 2.23/2.45  thf('4', plain,
% 2.23/2.45      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))),
% 2.23/2.45      inference('sup-', [status(thm)], ['2', '3'])).
% 2.23/2.45  thf('5', plain,
% 2.23/2.45      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.23/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.45  thf(cc1_relset_1, axiom,
% 2.23/2.45    (![A:$i,B:$i,C:$i]:
% 2.23/2.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.23/2.45       ( v1_relat_1 @ C ) ))).
% 2.23/2.45  thf('6', plain,
% 2.23/2.45      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.23/2.45         ((v1_relat_1 @ X15)
% 2.23/2.45          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 2.23/2.45      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.23/2.45  thf('7', plain, ((v1_relat_1 @ sk_C_1)),
% 2.23/2.45      inference('sup-', [status(thm)], ['5', '6'])).
% 2.23/2.45  thf('8', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)),
% 2.23/2.45      inference('demod', [status(thm)], ['4', '7'])).
% 2.23/2.45  thf('9', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 2.23/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.45  thf(d1_funct_2, axiom,
% 2.23/2.45    (![A:$i,B:$i,C:$i]:
% 2.23/2.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.23/2.45       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.23/2.45           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.23/2.45             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.23/2.45         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.23/2.45           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.23/2.45             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.23/2.45  thf(zf_stmt_1, axiom,
% 2.23/2.45    (![C:$i,B:$i,A:$i]:
% 2.23/2.45     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.23/2.45       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.23/2.45  thf('10', plain,
% 2.23/2.45      (![X30 : $i, X31 : $i, X32 : $i]:
% 2.23/2.45         (~ (v1_funct_2 @ X32 @ X30 @ X31)
% 2.23/2.45          | ((X30) = (k1_relset_1 @ X30 @ X31 @ X32))
% 2.23/2.45          | ~ (zip_tseitin_1 @ X32 @ X31 @ X30))),
% 2.23/2.45      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.23/2.45  thf('11', plain,
% 2.23/2.45      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 2.23/2.45        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 2.23/2.45      inference('sup-', [status(thm)], ['9', '10'])).
% 2.23/2.45  thf(zf_stmt_2, axiom,
% 2.23/2.45    (![B:$i,A:$i]:
% 2.23/2.45     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.23/2.45       ( zip_tseitin_0 @ B @ A ) ))).
% 2.23/2.45  thf('12', plain,
% 2.23/2.45      (![X28 : $i, X29 : $i]:
% 2.23/2.45         ((zip_tseitin_0 @ X28 @ X29) | ((X28) = (k1_xboole_0)))),
% 2.23/2.45      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.23/2.45  thf('13', plain,
% 2.23/2.45      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.23/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.45  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.23/2.45  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 2.23/2.45  thf(zf_stmt_5, axiom,
% 2.23/2.45    (![A:$i,B:$i,C:$i]:
% 2.23/2.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.23/2.45       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.23/2.45         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.23/2.45           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.23/2.45             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.23/2.45  thf('14', plain,
% 2.23/2.45      (![X33 : $i, X34 : $i, X35 : $i]:
% 2.23/2.45         (~ (zip_tseitin_0 @ X33 @ X34)
% 2.23/2.45          | (zip_tseitin_1 @ X35 @ X33 @ X34)
% 2.23/2.45          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33))))),
% 2.23/2.45      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.23/2.45  thf('15', plain,
% 2.23/2.45      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 2.23/2.45        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 2.23/2.45      inference('sup-', [status(thm)], ['13', '14'])).
% 2.23/2.45  thf('16', plain,
% 2.23/2.45      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A))),
% 2.23/2.45      inference('sup-', [status(thm)], ['12', '15'])).
% 2.23/2.45  thf('17', plain, (((sk_B_1) != (k1_xboole_0))),
% 2.23/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.45  thf('18', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)),
% 2.23/2.45      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 2.23/2.45  thf('19', plain,
% 2.23/2.45      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.23/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.45  thf(redefinition_k1_relset_1, axiom,
% 2.23/2.45    (![A:$i,B:$i,C:$i]:
% 2.23/2.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.23/2.45       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.23/2.45  thf('20', plain,
% 2.23/2.45      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.23/2.45         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 2.23/2.45          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 2.23/2.45      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.23/2.45  thf('21', plain,
% 2.23/2.45      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 2.23/2.45      inference('sup-', [status(thm)], ['19', '20'])).
% 2.23/2.45  thf('22', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 2.23/2.45      inference('demod', [status(thm)], ['11', '18', '21'])).
% 2.23/2.45  thf('23', plain,
% 2.23/2.45      (![X28 : $i, X29 : $i]:
% 2.23/2.45         ((zip_tseitin_0 @ X28 @ X29) | ((X28) = (k1_xboole_0)))),
% 2.23/2.45      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.23/2.45  thf(t65_relat_1, axiom,
% 2.23/2.45    (![A:$i]:
% 2.23/2.45     ( ( v1_relat_1 @ A ) =>
% 2.23/2.45       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 2.23/2.45         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 2.23/2.45  thf('24', plain,
% 2.23/2.45      (![X7 : $i]:
% 2.23/2.45         (((k1_relat_1 @ X7) != (k1_xboole_0))
% 2.23/2.45          | ((k2_relat_1 @ X7) = (k1_xboole_0))
% 2.23/2.45          | ~ (v1_relat_1 @ X7))),
% 2.23/2.45      inference('cnf', [status(esa)], [t65_relat_1])).
% 2.23/2.45  thf('25', plain,
% 2.23/2.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.23/2.45         (((k1_relat_1 @ X1) != (X0))
% 2.23/2.45          | (zip_tseitin_0 @ X0 @ X2)
% 2.23/2.45          | ~ (v1_relat_1 @ X1)
% 2.23/2.45          | ((k2_relat_1 @ X1) = (k1_xboole_0)))),
% 2.23/2.45      inference('sup-', [status(thm)], ['23', '24'])).
% 2.23/2.45  thf('26', plain,
% 2.23/2.45      (![X1 : $i, X2 : $i]:
% 2.23/2.45         (((k2_relat_1 @ X1) = (k1_xboole_0))
% 2.23/2.45          | ~ (v1_relat_1 @ X1)
% 2.23/2.45          | (zip_tseitin_0 @ (k1_relat_1 @ X1) @ X2))),
% 2.23/2.45      inference('simplify', [status(thm)], ['25'])).
% 2.23/2.45  thf('27', plain,
% 2.23/2.45      (![X0 : $i]:
% 2.23/2.45         ((zip_tseitin_0 @ sk_A @ X0)
% 2.23/2.45          | ~ (v1_relat_1 @ sk_C_1)
% 2.23/2.45          | ((k2_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 2.23/2.45      inference('sup+', [status(thm)], ['22', '26'])).
% 2.23/2.45  thf('28', plain, ((v1_relat_1 @ sk_C_1)),
% 2.23/2.45      inference('sup-', [status(thm)], ['5', '6'])).
% 2.23/2.45  thf('29', plain,
% 2.23/2.45      (![X0 : $i]:
% 2.23/2.45         ((zip_tseitin_0 @ sk_A @ X0) | ((k2_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 2.23/2.45      inference('demod', [status(thm)], ['27', '28'])).
% 2.23/2.45  thf('30', plain,
% 2.23/2.45      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 2.23/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.45  thf('31', plain,
% 2.23/2.45      (![X33 : $i, X34 : $i, X35 : $i]:
% 2.23/2.45         (~ (zip_tseitin_0 @ X33 @ X34)
% 2.23/2.45          | (zip_tseitin_1 @ X35 @ X33 @ X34)
% 2.23/2.45          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33))))),
% 2.23/2.45      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.23/2.45  thf('32', plain,
% 2.23/2.45      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B_1)
% 2.23/2.45        | ~ (zip_tseitin_0 @ sk_A @ sk_B_1))),
% 2.23/2.45      inference('sup-', [status(thm)], ['30', '31'])).
% 2.23/2.45  thf('33', plain,
% 2.23/2.45      ((((k2_relat_1 @ sk_C_1) = (k1_xboole_0))
% 2.23/2.45        | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B_1))),
% 2.23/2.45      inference('sup-', [status(thm)], ['29', '32'])).
% 2.23/2.45  thf('34', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 2.23/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.45  thf('35', plain,
% 2.23/2.45      (![X30 : $i, X31 : $i, X32 : $i]:
% 2.23/2.45         (~ (v1_funct_2 @ X32 @ X30 @ X31)
% 2.23/2.45          | ((X30) = (k1_relset_1 @ X30 @ X31 @ X32))
% 2.23/2.45          | ~ (zip_tseitin_1 @ X32 @ X31 @ X30))),
% 2.23/2.45      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.23/2.45  thf('36', plain,
% 2.23/2.45      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B_1)
% 2.23/2.45        | ((sk_B_1) = (k1_relset_1 @ sk_B_1 @ sk_A @ sk_D)))),
% 2.23/2.45      inference('sup-', [status(thm)], ['34', '35'])).
% 2.23/2.45  thf('37', plain,
% 2.23/2.45      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 2.23/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.45  thf('38', plain,
% 2.23/2.45      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.23/2.45         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 2.23/2.45          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 2.23/2.45      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.23/2.45  thf('39', plain,
% 2.23/2.45      (((k1_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 2.23/2.45      inference('sup-', [status(thm)], ['37', '38'])).
% 2.23/2.45  thf('40', plain,
% 2.23/2.45      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B_1)
% 2.23/2.45        | ((sk_B_1) = (k1_relat_1 @ sk_D)))),
% 2.23/2.45      inference('demod', [status(thm)], ['36', '39'])).
% 2.23/2.45  thf('41', plain,
% 2.23/2.45      ((((k2_relat_1 @ sk_C_1) = (k1_xboole_0))
% 2.23/2.45        | ((sk_B_1) = (k1_relat_1 @ sk_D)))),
% 2.23/2.45      inference('sup-', [status(thm)], ['33', '40'])).
% 2.23/2.45  thf(t144_funct_1, axiom,
% 2.23/2.45    (![A:$i]:
% 2.23/2.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.23/2.45       ( ( ![B:$i]:
% 2.23/2.45           ( ~( ( r2_hidden @ B @ ( k2_relat_1 @ A ) ) & 
% 2.23/2.45                ( ![C:$i]:
% 2.23/2.45                  ( ( k10_relat_1 @ A @ ( k1_tarski @ B ) ) !=
% 2.23/2.45                    ( k1_tarski @ C ) ) ) ) ) ) <=>
% 2.23/2.45         ( v2_funct_1 @ A ) ) ))).
% 2.23/2.45  thf('42', plain,
% 2.23/2.45      (![X10 : $i]:
% 2.23/2.45         ((r2_hidden @ (sk_B @ X10) @ (k2_relat_1 @ X10))
% 2.23/2.45          | (v2_funct_1 @ X10)
% 2.23/2.45          | ~ (v1_funct_1 @ X10)
% 2.23/2.45          | ~ (v1_relat_1 @ X10))),
% 2.23/2.45      inference('cnf', [status(esa)], [t144_funct_1])).
% 2.23/2.45  thf('43', plain,
% 2.23/2.45      (((r2_hidden @ (sk_B @ sk_C_1) @ k1_xboole_0)
% 2.23/2.45        | ((sk_B_1) = (k1_relat_1 @ sk_D))
% 2.23/2.45        | ~ (v1_relat_1 @ sk_C_1)
% 2.23/2.45        | ~ (v1_funct_1 @ sk_C_1)
% 2.23/2.45        | (v2_funct_1 @ sk_C_1))),
% 2.23/2.45      inference('sup+', [status(thm)], ['41', '42'])).
% 2.23/2.45  thf('44', plain, ((v1_relat_1 @ sk_C_1)),
% 2.23/2.45      inference('sup-', [status(thm)], ['5', '6'])).
% 2.23/2.45  thf('45', plain, ((v1_funct_1 @ sk_C_1)),
% 2.23/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.45  thf('46', plain,
% 2.23/2.45      (((r2_hidden @ (sk_B @ sk_C_1) @ k1_xboole_0)
% 2.23/2.45        | ((sk_B_1) = (k1_relat_1 @ sk_D))
% 2.23/2.45        | (v2_funct_1 @ sk_C_1))),
% 2.23/2.45      inference('demod', [status(thm)], ['43', '44', '45'])).
% 2.23/2.45  thf(t113_zfmisc_1, axiom,
% 2.23/2.45    (![A:$i,B:$i]:
% 2.23/2.45     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 2.23/2.45       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 2.23/2.45  thf('47', plain,
% 2.23/2.45      (![X1 : $i, X2 : $i]:
% 2.23/2.45         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 2.23/2.45      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.23/2.45  thf('48', plain,
% 2.23/2.45      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.23/2.45      inference('simplify', [status(thm)], ['47'])).
% 2.23/2.45  thf(t152_zfmisc_1, axiom,
% 2.23/2.45    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 2.23/2.45  thf('49', plain,
% 2.23/2.45      (![X3 : $i, X4 : $i]: ~ (r2_hidden @ X3 @ (k2_zfmisc_1 @ X3 @ X4))),
% 2.23/2.45      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 2.23/2.45  thf('50', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 2.23/2.45      inference('sup-', [status(thm)], ['48', '49'])).
% 2.23/2.45  thf('51', plain,
% 2.23/2.45      (((v2_funct_1 @ sk_C_1) | ((sk_B_1) = (k1_relat_1 @ sk_D)))),
% 2.23/2.45      inference('clc', [status(thm)], ['46', '50'])).
% 2.23/2.45  thf('52', plain, (~ (v2_funct_1 @ sk_C_1)),
% 2.23/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.45  thf('53', plain, (((sk_B_1) = (k1_relat_1 @ sk_D))),
% 2.23/2.45      inference('clc', [status(thm)], ['51', '52'])).
% 2.23/2.45  thf(t47_funct_1, axiom,
% 2.23/2.45    (![A:$i]:
% 2.23/2.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.23/2.45       ( ![B:$i]:
% 2.23/2.45         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.23/2.45           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 2.23/2.45               ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) =>
% 2.23/2.45             ( v2_funct_1 @ B ) ) ) ) ))).
% 2.23/2.45  thf('54', plain,
% 2.23/2.45      (![X13 : $i, X14 : $i]:
% 2.23/2.45         (~ (v1_relat_1 @ X13)
% 2.23/2.45          | ~ (v1_funct_1 @ X13)
% 2.23/2.45          | (v2_funct_1 @ X13)
% 2.23/2.45          | ~ (r1_tarski @ (k2_relat_1 @ X13) @ (k1_relat_1 @ X14))
% 2.23/2.45          | ~ (v2_funct_1 @ (k5_relat_1 @ X13 @ X14))
% 2.23/2.45          | ~ (v1_funct_1 @ X14)
% 2.23/2.45          | ~ (v1_relat_1 @ X14))),
% 2.23/2.45      inference('cnf', [status(esa)], [t47_funct_1])).
% 2.23/2.45  thf('55', plain,
% 2.23/2.45      (![X0 : $i]:
% 2.23/2.45         (~ (r1_tarski @ (k2_relat_1 @ X0) @ sk_B_1)
% 2.23/2.45          | ~ (v1_relat_1 @ sk_D)
% 2.23/2.45          | ~ (v1_funct_1 @ sk_D)
% 2.23/2.45          | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ sk_D))
% 2.23/2.45          | (v2_funct_1 @ X0)
% 2.23/2.45          | ~ (v1_funct_1 @ X0)
% 2.23/2.45          | ~ (v1_relat_1 @ X0))),
% 2.23/2.45      inference('sup-', [status(thm)], ['53', '54'])).
% 2.23/2.45  thf('56', plain,
% 2.23/2.45      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 2.23/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.45  thf('57', plain,
% 2.23/2.45      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.23/2.45         ((v1_relat_1 @ X15)
% 2.23/2.45          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 2.23/2.45      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.23/2.45  thf('58', plain, ((v1_relat_1 @ sk_D)),
% 2.23/2.45      inference('sup-', [status(thm)], ['56', '57'])).
% 2.23/2.45  thf('59', plain, ((v1_funct_1 @ sk_D)),
% 2.23/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.45  thf('60', plain,
% 2.23/2.45      (![X0 : $i]:
% 2.23/2.45         (~ (r1_tarski @ (k2_relat_1 @ X0) @ sk_B_1)
% 2.23/2.45          | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ sk_D))
% 2.23/2.45          | (v2_funct_1 @ X0)
% 2.23/2.45          | ~ (v1_funct_1 @ X0)
% 2.23/2.45          | ~ (v1_relat_1 @ X0))),
% 2.23/2.45      inference('demod', [status(thm)], ['55', '58', '59'])).
% 2.23/2.45  thf('61', plain,
% 2.23/2.45      ((~ (v1_relat_1 @ sk_C_1)
% 2.23/2.45        | ~ (v1_funct_1 @ sk_C_1)
% 2.23/2.45        | (v2_funct_1 @ sk_C_1)
% 2.23/2.45        | ~ (v2_funct_1 @ (k5_relat_1 @ sk_C_1 @ sk_D)))),
% 2.23/2.45      inference('sup-', [status(thm)], ['8', '60'])).
% 2.23/2.45  thf('62', plain, ((v1_relat_1 @ sk_C_1)),
% 2.23/2.45      inference('sup-', [status(thm)], ['5', '6'])).
% 2.23/2.45  thf('63', plain, ((v1_funct_1 @ sk_C_1)),
% 2.23/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.45  thf('64', plain,
% 2.23/2.45      (((v2_funct_1 @ sk_C_1) | ~ (v2_funct_1 @ (k5_relat_1 @ sk_C_1 @ sk_D)))),
% 2.23/2.45      inference('demod', [status(thm)], ['61', '62', '63'])).
% 2.23/2.45  thf('65', plain, (~ (v2_funct_1 @ sk_C_1)),
% 2.23/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.45  thf('66', plain, (~ (v2_funct_1 @ (k5_relat_1 @ sk_C_1 @ sk_D))),
% 2.23/2.45      inference('clc', [status(thm)], ['64', '65'])).
% 2.23/2.45  thf('67', plain,
% 2.23/2.45      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.23/2.45        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ 
% 2.23/2.45        (k6_partfun1 @ sk_A))),
% 2.23/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.45  thf(redefinition_k6_partfun1, axiom,
% 2.23/2.45    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 2.23/2.45  thf('68', plain, (![X50 : $i]: ((k6_partfun1 @ X50) = (k6_relat_1 @ X50))),
% 2.23/2.45      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.23/2.45  thf('69', plain,
% 2.23/2.45      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.23/2.45        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ 
% 2.23/2.45        (k6_relat_1 @ sk_A))),
% 2.23/2.45      inference('demod', [status(thm)], ['67', '68'])).
% 2.23/2.45  thf('70', plain,
% 2.23/2.45      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 2.23/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.45  thf('71', plain,
% 2.23/2.45      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.23/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.45  thf(redefinition_k1_partfun1, axiom,
% 2.23/2.45    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.23/2.45     ( ( ( v1_funct_1 @ E ) & 
% 2.23/2.45         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.23/2.45         ( v1_funct_1 @ F ) & 
% 2.23/2.45         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.23/2.45       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.23/2.45  thf('72', plain,
% 2.23/2.45      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 2.23/2.45         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 2.23/2.45          | ~ (v1_funct_1 @ X44)
% 2.23/2.45          | ~ (v1_funct_1 @ X47)
% 2.23/2.45          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 2.23/2.45          | ((k1_partfun1 @ X45 @ X46 @ X48 @ X49 @ X44 @ X47)
% 2.23/2.45              = (k5_relat_1 @ X44 @ X47)))),
% 2.23/2.45      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 2.23/2.45  thf('73', plain,
% 2.23/2.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.23/2.45         (((k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C_1 @ X0)
% 2.23/2.45            = (k5_relat_1 @ sk_C_1 @ X0))
% 2.23/2.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.23/2.45          | ~ (v1_funct_1 @ X0)
% 2.23/2.45          | ~ (v1_funct_1 @ sk_C_1))),
% 2.23/2.45      inference('sup-', [status(thm)], ['71', '72'])).
% 2.23/2.45  thf('74', plain, ((v1_funct_1 @ sk_C_1)),
% 2.23/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.45  thf('75', plain,
% 2.23/2.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.23/2.45         (((k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C_1 @ X0)
% 2.23/2.45            = (k5_relat_1 @ sk_C_1 @ X0))
% 2.23/2.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.23/2.45          | ~ (v1_funct_1 @ X0))),
% 2.23/2.45      inference('demod', [status(thm)], ['73', '74'])).
% 2.23/2.45  thf('76', plain,
% 2.23/2.45      ((~ (v1_funct_1 @ sk_D)
% 2.23/2.45        | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 2.23/2.45            = (k5_relat_1 @ sk_C_1 @ sk_D)))),
% 2.23/2.45      inference('sup-', [status(thm)], ['70', '75'])).
% 2.23/2.45  thf('77', plain, ((v1_funct_1 @ sk_D)),
% 2.23/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.45  thf('78', plain,
% 2.23/2.45      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 2.23/2.45         = (k5_relat_1 @ sk_C_1 @ sk_D))),
% 2.23/2.45      inference('demod', [status(thm)], ['76', '77'])).
% 2.23/2.45  thf('79', plain,
% 2.23/2.45      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C_1 @ sk_D) @ 
% 2.23/2.45        (k6_relat_1 @ sk_A))),
% 2.23/2.45      inference('demod', [status(thm)], ['69', '78'])).
% 2.23/2.45  thf('80', plain,
% 2.23/2.45      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 2.23/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.45  thf('81', plain,
% 2.23/2.45      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.23/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.45  thf(dt_k1_partfun1, axiom,
% 2.23/2.45    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.23/2.45     ( ( ( v1_funct_1 @ E ) & 
% 2.23/2.45         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.23/2.45         ( v1_funct_1 @ F ) & 
% 2.23/2.45         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.23/2.45       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.23/2.45         ( m1_subset_1 @
% 2.23/2.45           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.23/2.45           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 2.23/2.45  thf('82', plain,
% 2.23/2.45      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 2.23/2.45         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 2.23/2.45          | ~ (v1_funct_1 @ X36)
% 2.23/2.45          | ~ (v1_funct_1 @ X39)
% 2.23/2.45          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 2.23/2.45          | (m1_subset_1 @ (k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39) @ 
% 2.23/2.45             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X41))))),
% 2.23/2.45      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 2.23/2.45  thf('83', plain,
% 2.23/2.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.23/2.45         ((m1_subset_1 @ 
% 2.23/2.45           (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 2.23/2.45           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.23/2.45          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.23/2.45          | ~ (v1_funct_1 @ X1)
% 2.23/2.45          | ~ (v1_funct_1 @ sk_C_1))),
% 2.23/2.45      inference('sup-', [status(thm)], ['81', '82'])).
% 2.23/2.45  thf('84', plain, ((v1_funct_1 @ sk_C_1)),
% 2.23/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.45  thf('85', plain,
% 2.23/2.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.23/2.45         ((m1_subset_1 @ 
% 2.23/2.45           (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 2.23/2.45           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.23/2.45          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.23/2.45          | ~ (v1_funct_1 @ X1))),
% 2.23/2.45      inference('demod', [status(thm)], ['83', '84'])).
% 2.23/2.45  thf('86', plain,
% 2.23/2.45      ((~ (v1_funct_1 @ sk_D)
% 2.23/2.45        | (m1_subset_1 @ 
% 2.23/2.45           (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ 
% 2.23/2.45           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.23/2.45      inference('sup-', [status(thm)], ['80', '85'])).
% 2.23/2.45  thf('87', plain, ((v1_funct_1 @ sk_D)),
% 2.23/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.45  thf('88', plain,
% 2.23/2.45      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 2.23/2.45         = (k5_relat_1 @ sk_C_1 @ sk_D))),
% 2.23/2.45      inference('demod', [status(thm)], ['76', '77'])).
% 2.23/2.45  thf('89', plain,
% 2.23/2.45      ((m1_subset_1 @ (k5_relat_1 @ sk_C_1 @ sk_D) @ 
% 2.23/2.45        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.23/2.45      inference('demod', [status(thm)], ['86', '87', '88'])).
% 2.23/2.45  thf(redefinition_r2_relset_1, axiom,
% 2.23/2.45    (![A:$i,B:$i,C:$i,D:$i]:
% 2.23/2.45     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.23/2.45         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.23/2.45       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.23/2.45  thf('90', plain,
% 2.23/2.45      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 2.23/2.45         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 2.23/2.45          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 2.23/2.45          | ((X24) = (X27))
% 2.23/2.45          | ~ (r2_relset_1 @ X25 @ X26 @ X24 @ X27))),
% 2.23/2.45      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.23/2.45  thf('91', plain,
% 2.23/2.45      (![X0 : $i]:
% 2.23/2.45         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C_1 @ sk_D) @ X0)
% 2.23/2.45          | ((k5_relat_1 @ sk_C_1 @ sk_D) = (X0))
% 2.23/2.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.23/2.45      inference('sup-', [status(thm)], ['89', '90'])).
% 2.23/2.45  thf('92', plain,
% 2.23/2.45      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 2.23/2.45           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 2.23/2.45        | ((k5_relat_1 @ sk_C_1 @ sk_D) = (k6_relat_1 @ sk_A)))),
% 2.23/2.45      inference('sup-', [status(thm)], ['79', '91'])).
% 2.23/2.45  thf(dt_k6_partfun1, axiom,
% 2.23/2.45    (![A:$i]:
% 2.23/2.45     ( ( m1_subset_1 @
% 2.23/2.45         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 2.23/2.45       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 2.23/2.45  thf('93', plain,
% 2.23/2.45      (![X43 : $i]:
% 2.23/2.45         (m1_subset_1 @ (k6_partfun1 @ X43) @ 
% 2.23/2.45          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X43)))),
% 2.23/2.45      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 2.23/2.45  thf('94', plain, (![X50 : $i]: ((k6_partfun1 @ X50) = (k6_relat_1 @ X50))),
% 2.23/2.45      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.23/2.45  thf('95', plain,
% 2.23/2.45      (![X43 : $i]:
% 2.23/2.45         (m1_subset_1 @ (k6_relat_1 @ X43) @ 
% 2.23/2.45          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X43)))),
% 2.23/2.45      inference('demod', [status(thm)], ['93', '94'])).
% 2.23/2.45  thf('96', plain, (((k5_relat_1 @ sk_C_1 @ sk_D) = (k6_relat_1 @ sk_A))),
% 2.23/2.45      inference('demod', [status(thm)], ['92', '95'])).
% 2.23/2.45  thf(fc4_funct_1, axiom,
% 2.23/2.45    (![A:$i]:
% 2.23/2.45     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 2.23/2.45       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 2.23/2.45  thf('97', plain, (![X9 : $i]: (v2_funct_1 @ (k6_relat_1 @ X9))),
% 2.23/2.45      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.23/2.45  thf('98', plain, ($false),
% 2.23/2.45      inference('demod', [status(thm)], ['66', '96', '97'])).
% 2.23/2.45  
% 2.23/2.45  % SZS output end Refutation
% 2.23/2.45  
% 2.23/2.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
