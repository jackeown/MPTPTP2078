%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.biTiFrkw8B

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:20 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 190 expanded)
%              Number of leaves         :   45 (  75 expanded)
%              Depth                    :   19
%              Number of atoms          :  922 (1990 expanded)
%              Number of equality atoms :   65 ( 111 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(t190_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ B @ C )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
     => ~ ( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) )
          & ! [E: $i] :
              ( ( m1_subset_1 @ E @ B )
             => ( A
               != ( k1_funct_1 @ D @ E ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ B @ C )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
       => ~ ( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) )
            & ! [E: $i] :
                ( ( m1_subset_1 @ E @ B )
               => ( A
                 != ( k1_funct_1 @ D @ E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t190_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( ( k2_relset_1 @ X41 @ X42 @ X40 )
        = ( k2_relat_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_3 )
    = ( k2_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X28: $i,X30: $i,X31: $i] :
      ( ( X30
       != ( k2_relat_1 @ X28 ) )
      | ( r2_hidden @ ( sk_D_2 @ X31 @ X28 ) @ ( k1_relat_1 @ X28 ) )
      | ~ ( r2_hidden @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('6',plain,(
    ! [X28: $i,X31: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( r2_hidden @ X31 @ ( k2_relat_1 @ X28 ) )
      | ( r2_hidden @ ( sk_D_2 @ X31 @ X28 ) @ ( k1_relat_1 @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_A @ sk_D_3 ) @ ( k1_relat_1 @ sk_D_3 ) )
    | ~ ( v1_funct_1 @ sk_D_3 )
    | ~ ( v1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('10',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( v1_relat_1 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) )
    | ( v1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('12',plain,(
    ! [X25: $i,X26: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('13',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    r2_hidden @ ( sk_D_2 @ sk_A @ sk_D_3 ) @ ( k1_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['7','8','13'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('15',plain,(
    ! [X19: $i,X20: $i] :
      ( ( m1_subset_1 @ X19 @ X20 )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('16',plain,(
    m1_subset_1 @ ( sk_D_2 @ sk_A @ sk_D_3 ) @ ( k1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_2 @ sk_D_3 @ sk_B @ sk_C_1 ),
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

thf('18',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( v1_funct_2 @ X47 @ X45 @ X46 )
      | ( X45
        = ( k1_relset_1 @ X45 @ X46 @ X47 ) )
      | ~ ( zip_tseitin_1 @ X47 @ X46 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('19',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ sk_C_1 @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k1_relset_1 @ X38 @ X39 @ X37 )
        = ( k1_relat_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C_1 @ sk_D_3 )
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ sk_C_1 @ sk_B )
    | ( sk_B
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('25',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( zip_tseitin_0 @ X48 @ X49 )
      | ( zip_tseitin_1 @ X50 @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('26',plain,
    ( ( zip_tseitin_1 @ sk_D_3 @ sk_C_1 @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X43: $i,X44: $i] :
      ( ( zip_tseitin_0 @ X43 @ X44 )
      | ( X43 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('28',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['28'])).

thf('30',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['28'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('35',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X14 ) @ X16 )
      | ~ ( r2_hidden @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k1_tarski @ ( sk_D @ X1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('37',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_D @ X1 @ X1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('39',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X17 ) @ X18 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( X1
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X1: $i] :
      ( X1
      = ( k2_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['27','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('44',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v5_relat_1 @ X34 @ X36 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('45',plain,(
    v5_relat_1 @ sk_D_3 @ sk_C_1 ),
    inference('sup-',[status(thm)],['43','44'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('46',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v5_relat_1 @ X23 @ X24 )
      | ( r1_tarski @ ( k2_relat_1 @ X23 ) @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ sk_D_3 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_3 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['11','12'])).

thf('49',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_3 ) @ sk_C_1 ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('51',plain,
    ( ( k2_xboole_0 @ ( k2_relat_1 @ sk_D_3 ) @ sk_C_1 )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    r2_hidden @ sk_A @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ ( k2_xboole_0 @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_3 )
    = ( k2_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('57',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_D_3 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    r2_hidden @ sk_A @ sk_C_1 ),
    inference('sup+',[status(thm)],['51','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('60',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X14 ) @ X16 )
      | ~ ( r2_hidden @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_xboole_0 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_xboole_0 @ sk_C_1 @ X0 ) )
      = ( k2_xboole_0 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X17 ) @ X18 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_C_1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_C_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['42','66'])).

thf('68',plain,(
    ! [X1: $i] :
      ( zip_tseitin_0 @ sk_C_1 @ X1 ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    zip_tseitin_1 @ sk_D_3 @ sk_C_1 @ sk_B ),
    inference(demod,[status(thm)],['26','68'])).

thf('70',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['23','69'])).

thf('71',plain,(
    m1_subset_1 @ ( sk_D_2 @ sk_A @ sk_D_3 ) @ sk_B ),
    inference(demod,[status(thm)],['16','70'])).

thf('72',plain,(
    ! [X51: $i] :
      ( ( sk_A
       != ( k1_funct_1 @ sk_D_3 @ X51 ) )
      | ~ ( m1_subset_1 @ X51 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    sk_A
 != ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_A @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('75',plain,(
    ! [X28: $i,X30: $i,X31: $i] :
      ( ( X30
       != ( k2_relat_1 @ X28 ) )
      | ( X31
        = ( k1_funct_1 @ X28 @ ( sk_D_2 @ X31 @ X28 ) ) )
      | ~ ( r2_hidden @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('76',plain,(
    ! [X28: $i,X31: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( r2_hidden @ X31 @ ( k2_relat_1 @ X28 ) )
      | ( X31
        = ( k1_funct_1 @ X28 @ ( sk_D_2 @ X31 @ X28 ) ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ( sk_A
      = ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_A @ sk_D_3 ) ) )
    | ~ ( v1_funct_1 @ sk_D_3 )
    | ~ ( v1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['74','76'])).

thf('78',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['11','12'])).

thf('80',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_A @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['73','80'])).

thf('82',plain,(
    $false ),
    inference(simplify,[status(thm)],['81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.biTiFrkw8B
% 0.13/0.37  % Computer   : n024.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 18:39:51 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.50/0.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.50/0.74  % Solved by: fo/fo7.sh
% 0.50/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.74  % done 306 iterations in 0.259s
% 0.50/0.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.50/0.74  % SZS output start Refutation
% 0.50/0.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.50/0.74  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.50/0.74  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.50/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.50/0.74  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.50/0.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.50/0.74  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 0.50/0.74  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.50/0.74  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.50/0.74  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.50/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.74  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.50/0.74  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.50/0.74  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.50/0.74  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.50/0.74  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.50/0.74  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.50/0.74  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.50/0.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.50/0.74  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.50/0.74  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.50/0.74  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.50/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.50/0.74  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.50/0.74  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.50/0.74  thf(t190_funct_2, conjecture,
% 0.50/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.74     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.50/0.74         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.50/0.74       ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.50/0.74            ( ![E:$i]:
% 0.50/0.74              ( ( m1_subset_1 @ E @ B ) => ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ))).
% 0.50/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.74    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.74        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.50/0.74            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.50/0.74          ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.50/0.74               ( ![E:$i]:
% 0.50/0.74                 ( ( m1_subset_1 @ E @ B ) =>
% 0.50/0.74                   ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) )),
% 0.50/0.74    inference('cnf.neg', [status(esa)], [t190_funct_2])).
% 0.50/0.74  thf('0', plain,
% 0.50/0.74      ((r2_hidden @ sk_A @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_3))),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('1', plain,
% 0.50/0.74      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf(redefinition_k2_relset_1, axiom,
% 0.50/0.74    (![A:$i,B:$i,C:$i]:
% 0.50/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.74       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.50/0.74  thf('2', plain,
% 0.50/0.74      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.50/0.74         (((k2_relset_1 @ X41 @ X42 @ X40) = (k2_relat_1 @ X40))
% 0.50/0.74          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42))))),
% 0.50/0.74      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.50/0.74  thf('3', plain,
% 0.50/0.74      (((k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_3) = (k2_relat_1 @ sk_D_3))),
% 0.50/0.74      inference('sup-', [status(thm)], ['1', '2'])).
% 0.50/0.74  thf('4', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_3))),
% 0.50/0.74      inference('demod', [status(thm)], ['0', '3'])).
% 0.50/0.74  thf(d5_funct_1, axiom,
% 0.50/0.74    (![A:$i]:
% 0.50/0.74     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.50/0.74       ( ![B:$i]:
% 0.50/0.74         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.50/0.74           ( ![C:$i]:
% 0.50/0.74             ( ( r2_hidden @ C @ B ) <=>
% 0.50/0.74               ( ?[D:$i]:
% 0.50/0.74                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.50/0.74                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.50/0.74  thf('5', plain,
% 0.50/0.74      (![X28 : $i, X30 : $i, X31 : $i]:
% 0.50/0.74         (((X30) != (k2_relat_1 @ X28))
% 0.50/0.74          | (r2_hidden @ (sk_D_2 @ X31 @ X28) @ (k1_relat_1 @ X28))
% 0.50/0.74          | ~ (r2_hidden @ X31 @ X30)
% 0.50/0.74          | ~ (v1_funct_1 @ X28)
% 0.50/0.74          | ~ (v1_relat_1 @ X28))),
% 0.50/0.74      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.50/0.74  thf('6', plain,
% 0.50/0.74      (![X28 : $i, X31 : $i]:
% 0.50/0.74         (~ (v1_relat_1 @ X28)
% 0.50/0.74          | ~ (v1_funct_1 @ X28)
% 0.50/0.74          | ~ (r2_hidden @ X31 @ (k2_relat_1 @ X28))
% 0.50/0.74          | (r2_hidden @ (sk_D_2 @ X31 @ X28) @ (k1_relat_1 @ X28)))),
% 0.50/0.74      inference('simplify', [status(thm)], ['5'])).
% 0.50/0.74  thf('7', plain,
% 0.50/0.74      (((r2_hidden @ (sk_D_2 @ sk_A @ sk_D_3) @ (k1_relat_1 @ sk_D_3))
% 0.50/0.74        | ~ (v1_funct_1 @ sk_D_3)
% 0.50/0.74        | ~ (v1_relat_1 @ sk_D_3))),
% 0.50/0.74      inference('sup-', [status(thm)], ['4', '6'])).
% 0.50/0.74  thf('8', plain, ((v1_funct_1 @ sk_D_3)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('9', plain,
% 0.50/0.74      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf(cc2_relat_1, axiom,
% 0.50/0.74    (![A:$i]:
% 0.50/0.74     ( ( v1_relat_1 @ A ) =>
% 0.50/0.74       ( ![B:$i]:
% 0.50/0.74         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.50/0.74  thf('10', plain,
% 0.50/0.74      (![X21 : $i, X22 : $i]:
% 0.50/0.74         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 0.50/0.74          | (v1_relat_1 @ X21)
% 0.50/0.74          | ~ (v1_relat_1 @ X22))),
% 0.50/0.74      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.50/0.74  thf('11', plain,
% 0.50/0.74      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)) | (v1_relat_1 @ sk_D_3))),
% 0.50/0.74      inference('sup-', [status(thm)], ['9', '10'])).
% 0.50/0.74  thf(fc6_relat_1, axiom,
% 0.50/0.74    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.50/0.74  thf('12', plain,
% 0.50/0.74      (![X25 : $i, X26 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X25 @ X26))),
% 0.50/0.74      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.50/0.74  thf('13', plain, ((v1_relat_1 @ sk_D_3)),
% 0.50/0.74      inference('demod', [status(thm)], ['11', '12'])).
% 0.50/0.74  thf('14', plain,
% 0.50/0.74      ((r2_hidden @ (sk_D_2 @ sk_A @ sk_D_3) @ (k1_relat_1 @ sk_D_3))),
% 0.50/0.74      inference('demod', [status(thm)], ['7', '8', '13'])).
% 0.50/0.74  thf(t1_subset, axiom,
% 0.50/0.74    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.50/0.74  thf('15', plain,
% 0.50/0.74      (![X19 : $i, X20 : $i]:
% 0.50/0.74         ((m1_subset_1 @ X19 @ X20) | ~ (r2_hidden @ X19 @ X20))),
% 0.50/0.74      inference('cnf', [status(esa)], [t1_subset])).
% 0.50/0.74  thf('16', plain,
% 0.50/0.74      ((m1_subset_1 @ (sk_D_2 @ sk_A @ sk_D_3) @ (k1_relat_1 @ sk_D_3))),
% 0.50/0.74      inference('sup-', [status(thm)], ['14', '15'])).
% 0.50/0.74  thf('17', plain, ((v1_funct_2 @ sk_D_3 @ sk_B @ sk_C_1)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf(d1_funct_2, axiom,
% 0.50/0.74    (![A:$i,B:$i,C:$i]:
% 0.50/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.74       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.50/0.74           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.50/0.74             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.50/0.74         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.50/0.74           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.50/0.74             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.50/0.74  thf(zf_stmt_1, axiom,
% 0.50/0.74    (![C:$i,B:$i,A:$i]:
% 0.50/0.74     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.50/0.74       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.50/0.74  thf('18', plain,
% 0.50/0.74      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.50/0.74         (~ (v1_funct_2 @ X47 @ X45 @ X46)
% 0.50/0.74          | ((X45) = (k1_relset_1 @ X45 @ X46 @ X47))
% 0.50/0.74          | ~ (zip_tseitin_1 @ X47 @ X46 @ X45))),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.50/0.74  thf('19', plain,
% 0.50/0.74      ((~ (zip_tseitin_1 @ sk_D_3 @ sk_C_1 @ sk_B)
% 0.50/0.74        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C_1 @ sk_D_3)))),
% 0.50/0.74      inference('sup-', [status(thm)], ['17', '18'])).
% 0.50/0.74  thf('20', plain,
% 0.50/0.74      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf(redefinition_k1_relset_1, axiom,
% 0.50/0.74    (![A:$i,B:$i,C:$i]:
% 0.50/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.74       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.50/0.74  thf('21', plain,
% 0.50/0.74      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.50/0.74         (((k1_relset_1 @ X38 @ X39 @ X37) = (k1_relat_1 @ X37))
% 0.50/0.74          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 0.50/0.74      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.50/0.74  thf('22', plain,
% 0.50/0.74      (((k1_relset_1 @ sk_B @ sk_C_1 @ sk_D_3) = (k1_relat_1 @ sk_D_3))),
% 0.50/0.74      inference('sup-', [status(thm)], ['20', '21'])).
% 0.50/0.74  thf('23', plain,
% 0.50/0.74      ((~ (zip_tseitin_1 @ sk_D_3 @ sk_C_1 @ sk_B)
% 0.50/0.74        | ((sk_B) = (k1_relat_1 @ sk_D_3)))),
% 0.50/0.74      inference('demod', [status(thm)], ['19', '22'])).
% 0.50/0.74  thf('24', plain,
% 0.50/0.74      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.50/0.74  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.50/0.74  thf(zf_stmt_4, axiom,
% 0.50/0.74    (![B:$i,A:$i]:
% 0.50/0.74     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.50/0.74       ( zip_tseitin_0 @ B @ A ) ))).
% 0.50/0.74  thf(zf_stmt_5, axiom,
% 0.50/0.74    (![A:$i,B:$i,C:$i]:
% 0.50/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.74       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.50/0.74         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.50/0.74           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.50/0.74             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.50/0.74  thf('25', plain,
% 0.50/0.74      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.50/0.74         (~ (zip_tseitin_0 @ X48 @ X49)
% 0.50/0.74          | (zip_tseitin_1 @ X50 @ X48 @ X49)
% 0.50/0.74          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X48))))),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.50/0.74  thf('26', plain,
% 0.50/0.74      (((zip_tseitin_1 @ sk_D_3 @ sk_C_1 @ sk_B)
% 0.50/0.74        | ~ (zip_tseitin_0 @ sk_C_1 @ sk_B))),
% 0.50/0.74      inference('sup-', [status(thm)], ['24', '25'])).
% 0.50/0.74  thf('27', plain,
% 0.50/0.74      (![X43 : $i, X44 : $i]:
% 0.50/0.74         ((zip_tseitin_0 @ X43 @ X44) | ((X43) = (k1_xboole_0)))),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.50/0.74  thf(d3_xboole_0, axiom,
% 0.50/0.74    (![A:$i,B:$i,C:$i]:
% 0.50/0.74     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.50/0.74       ( ![D:$i]:
% 0.50/0.74         ( ( r2_hidden @ D @ C ) <=>
% 0.50/0.74           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.50/0.74  thf('28', plain,
% 0.50/0.74      (![X1 : $i, X3 : $i, X5 : $i]:
% 0.50/0.74         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 0.50/0.74          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X1)
% 0.50/0.74          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X3)
% 0.50/0.74          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 0.50/0.74      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.50/0.74  thf('29', plain,
% 0.50/0.74      (![X0 : $i, X1 : $i]:
% 0.50/0.74         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.50/0.74          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.50/0.74          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 0.50/0.74      inference('eq_fact', [status(thm)], ['28'])).
% 0.50/0.74  thf('30', plain,
% 0.50/0.74      (![X1 : $i, X3 : $i, X5 : $i]:
% 0.50/0.74         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 0.50/0.74          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X1)
% 0.50/0.74          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 0.50/0.74      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.50/0.74  thf('31', plain,
% 0.50/0.74      (![X0 : $i, X1 : $i]:
% 0.50/0.74         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 0.50/0.74          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.50/0.74          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.50/0.74          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 0.50/0.74      inference('sup-', [status(thm)], ['29', '30'])).
% 0.50/0.74  thf('32', plain,
% 0.50/0.74      (![X0 : $i, X1 : $i]:
% 0.50/0.74         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.50/0.74          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.50/0.74          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 0.50/0.74      inference('simplify', [status(thm)], ['31'])).
% 0.50/0.74  thf('33', plain,
% 0.50/0.74      (![X0 : $i, X1 : $i]:
% 0.50/0.74         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.50/0.74          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.50/0.74          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 0.50/0.74      inference('eq_fact', [status(thm)], ['28'])).
% 0.50/0.74  thf('34', plain,
% 0.50/0.74      (![X0 : $i, X1 : $i]:
% 0.50/0.74         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 0.50/0.74          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 0.50/0.74      inference('clc', [status(thm)], ['32', '33'])).
% 0.50/0.74  thf(l1_zfmisc_1, axiom,
% 0.50/0.74    (![A:$i,B:$i]:
% 0.50/0.74     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.50/0.74  thf('35', plain,
% 0.50/0.74      (![X14 : $i, X16 : $i]:
% 0.50/0.74         ((r1_tarski @ (k1_tarski @ X14) @ X16) | ~ (r2_hidden @ X14 @ X16))),
% 0.50/0.74      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.50/0.74  thf('36', plain,
% 0.50/0.74      (![X0 : $i, X1 : $i]:
% 0.50/0.74         (((X1) = (k2_xboole_0 @ X0 @ X1))
% 0.50/0.74          | (r1_tarski @ (k1_tarski @ (sk_D @ X1 @ X1 @ X0)) @ X0))),
% 0.50/0.74      inference('sup-', [status(thm)], ['34', '35'])).
% 0.50/0.74  thf(t12_xboole_1, axiom,
% 0.50/0.74    (![A:$i,B:$i]:
% 0.50/0.74     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.50/0.74  thf('37', plain,
% 0.50/0.74      (![X6 : $i, X7 : $i]:
% 0.50/0.74         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.50/0.74      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.50/0.74  thf('38', plain,
% 0.50/0.74      (![X0 : $i, X1 : $i]:
% 0.50/0.74         (((X1) = (k2_xboole_0 @ X0 @ X1))
% 0.50/0.74          | ((k2_xboole_0 @ (k1_tarski @ (sk_D @ X1 @ X1 @ X0)) @ X0) = (X0)))),
% 0.50/0.74      inference('sup-', [status(thm)], ['36', '37'])).
% 0.50/0.74  thf(t49_zfmisc_1, axiom,
% 0.50/0.74    (![A:$i,B:$i]:
% 0.50/0.74     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.50/0.74  thf('39', plain,
% 0.50/0.74      (![X17 : $i, X18 : $i]:
% 0.50/0.74         ((k2_xboole_0 @ (k1_tarski @ X17) @ X18) != (k1_xboole_0))),
% 0.50/0.74      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.50/0.74  thf('40', plain,
% 0.50/0.74      (![X0 : $i, X1 : $i]:
% 0.50/0.74         (((X0) != (k1_xboole_0)) | ((X1) = (k2_xboole_0 @ X0 @ X1)))),
% 0.50/0.74      inference('sup-', [status(thm)], ['38', '39'])).
% 0.50/0.74  thf('41', plain, (![X1 : $i]: ((X1) = (k2_xboole_0 @ k1_xboole_0 @ X1))),
% 0.50/0.74      inference('simplify', [status(thm)], ['40'])).
% 0.50/0.74  thf('42', plain,
% 0.50/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.74         (((X1) = (k2_xboole_0 @ X0 @ X1)) | (zip_tseitin_0 @ X0 @ X2))),
% 0.50/0.74      inference('sup+', [status(thm)], ['27', '41'])).
% 0.50/0.74  thf('43', plain,
% 0.50/0.74      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf(cc2_relset_1, axiom,
% 0.50/0.74    (![A:$i,B:$i,C:$i]:
% 0.50/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.74       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.50/0.74  thf('44', plain,
% 0.50/0.74      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.50/0.74         ((v5_relat_1 @ X34 @ X36)
% 0.50/0.74          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.50/0.74      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.50/0.74  thf('45', plain, ((v5_relat_1 @ sk_D_3 @ sk_C_1)),
% 0.50/0.74      inference('sup-', [status(thm)], ['43', '44'])).
% 0.50/0.74  thf(d19_relat_1, axiom,
% 0.50/0.74    (![A:$i,B:$i]:
% 0.50/0.74     ( ( v1_relat_1 @ B ) =>
% 0.50/0.74       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.50/0.74  thf('46', plain,
% 0.50/0.74      (![X23 : $i, X24 : $i]:
% 0.50/0.74         (~ (v5_relat_1 @ X23 @ X24)
% 0.50/0.74          | (r1_tarski @ (k2_relat_1 @ X23) @ X24)
% 0.50/0.74          | ~ (v1_relat_1 @ X23))),
% 0.50/0.74      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.50/0.74  thf('47', plain,
% 0.50/0.74      ((~ (v1_relat_1 @ sk_D_3) | (r1_tarski @ (k2_relat_1 @ sk_D_3) @ sk_C_1))),
% 0.50/0.74      inference('sup-', [status(thm)], ['45', '46'])).
% 0.50/0.74  thf('48', plain, ((v1_relat_1 @ sk_D_3)),
% 0.50/0.74      inference('demod', [status(thm)], ['11', '12'])).
% 0.50/0.74  thf('49', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_3) @ sk_C_1)),
% 0.50/0.74      inference('demod', [status(thm)], ['47', '48'])).
% 0.50/0.74  thf('50', plain,
% 0.50/0.74      (![X6 : $i, X7 : $i]:
% 0.50/0.74         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.50/0.74      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.50/0.74  thf('51', plain,
% 0.50/0.74      (((k2_xboole_0 @ (k2_relat_1 @ sk_D_3) @ sk_C_1) = (sk_C_1))),
% 0.50/0.74      inference('sup-', [status(thm)], ['49', '50'])).
% 0.50/0.74  thf('52', plain,
% 0.50/0.74      ((r2_hidden @ sk_A @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_3))),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('53', plain,
% 0.50/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.50/0.74         (~ (r2_hidden @ X0 @ X3)
% 0.50/0.74          | (r2_hidden @ X0 @ X2)
% 0.50/0.74          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.50/0.74      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.50/0.74  thf('54', plain,
% 0.50/0.74      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.50/0.74         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 0.50/0.74      inference('simplify', [status(thm)], ['53'])).
% 0.50/0.74  thf('55', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         (r2_hidden @ sk_A @ 
% 0.50/0.74          (k2_xboole_0 @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_3) @ X0))),
% 0.50/0.74      inference('sup-', [status(thm)], ['52', '54'])).
% 0.50/0.74  thf('56', plain,
% 0.50/0.74      (((k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_3) = (k2_relat_1 @ sk_D_3))),
% 0.50/0.74      inference('sup-', [status(thm)], ['1', '2'])).
% 0.50/0.74  thf('57', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         (r2_hidden @ sk_A @ (k2_xboole_0 @ (k2_relat_1 @ sk_D_3) @ X0))),
% 0.50/0.74      inference('demod', [status(thm)], ['55', '56'])).
% 0.50/0.74  thf('58', plain, ((r2_hidden @ sk_A @ sk_C_1)),
% 0.50/0.74      inference('sup+', [status(thm)], ['51', '57'])).
% 0.50/0.74  thf('59', plain,
% 0.50/0.74      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.50/0.74         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 0.50/0.74      inference('simplify', [status(thm)], ['53'])).
% 0.50/0.74  thf('60', plain,
% 0.50/0.74      (![X0 : $i]: (r2_hidden @ sk_A @ (k2_xboole_0 @ sk_C_1 @ X0))),
% 0.50/0.74      inference('sup-', [status(thm)], ['58', '59'])).
% 0.50/0.74  thf('61', plain,
% 0.50/0.74      (![X14 : $i, X16 : $i]:
% 0.50/0.74         ((r1_tarski @ (k1_tarski @ X14) @ X16) | ~ (r2_hidden @ X14 @ X16))),
% 0.50/0.74      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.50/0.74  thf('62', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         (r1_tarski @ (k1_tarski @ sk_A) @ (k2_xboole_0 @ sk_C_1 @ X0))),
% 0.50/0.74      inference('sup-', [status(thm)], ['60', '61'])).
% 0.50/0.74  thf('63', plain,
% 0.50/0.74      (![X6 : $i, X7 : $i]:
% 0.50/0.74         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.50/0.74      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.50/0.74  thf('64', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         ((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_xboole_0 @ sk_C_1 @ X0))
% 0.50/0.74           = (k2_xboole_0 @ sk_C_1 @ X0))),
% 0.50/0.74      inference('sup-', [status(thm)], ['62', '63'])).
% 0.50/0.74  thf('65', plain,
% 0.50/0.74      (![X17 : $i, X18 : $i]:
% 0.50/0.74         ((k2_xboole_0 @ (k1_tarski @ X17) @ X18) != (k1_xboole_0))),
% 0.50/0.74      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.50/0.74  thf('66', plain,
% 0.50/0.74      (![X0 : $i]: ((k2_xboole_0 @ sk_C_1 @ X0) != (k1_xboole_0))),
% 0.50/0.74      inference('sup-', [status(thm)], ['64', '65'])).
% 0.50/0.74  thf('67', plain,
% 0.50/0.74      (![X0 : $i, X1 : $i]:
% 0.50/0.74         (((X0) != (k1_xboole_0)) | (zip_tseitin_0 @ sk_C_1 @ X1))),
% 0.50/0.74      inference('sup-', [status(thm)], ['42', '66'])).
% 0.50/0.74  thf('68', plain, (![X1 : $i]: (zip_tseitin_0 @ sk_C_1 @ X1)),
% 0.50/0.74      inference('simplify', [status(thm)], ['67'])).
% 0.50/0.74  thf('69', plain, ((zip_tseitin_1 @ sk_D_3 @ sk_C_1 @ sk_B)),
% 0.50/0.74      inference('demod', [status(thm)], ['26', '68'])).
% 0.50/0.74  thf('70', plain, (((sk_B) = (k1_relat_1 @ sk_D_3))),
% 0.50/0.74      inference('demod', [status(thm)], ['23', '69'])).
% 0.50/0.74  thf('71', plain, ((m1_subset_1 @ (sk_D_2 @ sk_A @ sk_D_3) @ sk_B)),
% 0.50/0.74      inference('demod', [status(thm)], ['16', '70'])).
% 0.50/0.74  thf('72', plain,
% 0.50/0.74      (![X51 : $i]:
% 0.50/0.74         (((sk_A) != (k1_funct_1 @ sk_D_3 @ X51))
% 0.50/0.74          | ~ (m1_subset_1 @ X51 @ sk_B))),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('73', plain,
% 0.50/0.74      (((sk_A) != (k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_A @ sk_D_3)))),
% 0.50/0.74      inference('sup-', [status(thm)], ['71', '72'])).
% 0.50/0.74  thf('74', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_3))),
% 0.50/0.74      inference('demod', [status(thm)], ['0', '3'])).
% 0.50/0.74  thf('75', plain,
% 0.50/0.74      (![X28 : $i, X30 : $i, X31 : $i]:
% 0.50/0.74         (((X30) != (k2_relat_1 @ X28))
% 0.50/0.74          | ((X31) = (k1_funct_1 @ X28 @ (sk_D_2 @ X31 @ X28)))
% 0.50/0.74          | ~ (r2_hidden @ X31 @ X30)
% 0.50/0.74          | ~ (v1_funct_1 @ X28)
% 0.50/0.74          | ~ (v1_relat_1 @ X28))),
% 0.50/0.74      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.50/0.74  thf('76', plain,
% 0.50/0.74      (![X28 : $i, X31 : $i]:
% 0.50/0.74         (~ (v1_relat_1 @ X28)
% 0.50/0.74          | ~ (v1_funct_1 @ X28)
% 0.50/0.74          | ~ (r2_hidden @ X31 @ (k2_relat_1 @ X28))
% 0.50/0.74          | ((X31) = (k1_funct_1 @ X28 @ (sk_D_2 @ X31 @ X28))))),
% 0.50/0.74      inference('simplify', [status(thm)], ['75'])).
% 0.50/0.74  thf('77', plain,
% 0.50/0.74      ((((sk_A) = (k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_A @ sk_D_3)))
% 0.50/0.74        | ~ (v1_funct_1 @ sk_D_3)
% 0.50/0.74        | ~ (v1_relat_1 @ sk_D_3))),
% 0.50/0.74      inference('sup-', [status(thm)], ['74', '76'])).
% 0.50/0.74  thf('78', plain, ((v1_funct_1 @ sk_D_3)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('79', plain, ((v1_relat_1 @ sk_D_3)),
% 0.50/0.74      inference('demod', [status(thm)], ['11', '12'])).
% 0.50/0.74  thf('80', plain,
% 0.50/0.74      (((sk_A) = (k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_A @ sk_D_3)))),
% 0.50/0.74      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.50/0.74  thf('81', plain, (((sk_A) != (sk_A))),
% 0.50/0.74      inference('demod', [status(thm)], ['73', '80'])).
% 0.50/0.74  thf('82', plain, ($false), inference('simplify', [status(thm)], ['81'])).
% 0.50/0.74  
% 0.50/0.74  % SZS output end Refutation
% 0.50/0.74  
% 0.57/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
