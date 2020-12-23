%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Vmxy6SJDDP

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:27 EST 2020

% Result     : Theorem 3.91s
% Output     : Refutation 3.91s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 190 expanded)
%              Number of leaves         :   38 (  71 expanded)
%              Depth                    :   20
%              Number of atoms          :  936 (2105 expanded)
%              Number of equality atoms :   86 ( 170 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t65_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( k1_funct_1 @ D @ C )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
       => ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ D @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v5_relat_1 @ X33 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('3',plain,(
    v5_relat_1 @ sk_D_3 @ ( k1_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

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

thf('4',plain,(
    ! [X41: $i,X42: $i] :
      ( ( zip_tseitin_0 @ X41 @ X42 )
      | ( X41 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('5',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
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
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( zip_tseitin_0 @ X46 @ X47 )
      | ( zip_tseitin_1 @ X48 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('7',plain,
    ( ( zip_tseitin_1 @ sk_D_3 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ~ ( zip_tseitin_0 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_3 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    v1_funct_2 @ sk_D_3 @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_funct_2 @ X45 @ X43 @ X44 )
      | ( X43
        = ( k1_relset_1 @ X43 @ X44 @ X45 ) )
      | ~ ( zip_tseitin_1 @ X45 @ X44 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('11',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('13',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k1_relset_1 @ X37 @ X38 @ X36 )
        = ( k1_relat_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('14',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D_3 )
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('16',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf(l44_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('17',plain,(
    ! [X20: $i,X21: $i] :
      ( ( X20 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X21 @ X20 ) @ X20 )
      | ( X20
        = ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('18',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('19',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X20: $i,X21: $i] :
      ( ( X20 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X21 @ X20 ) @ X20 )
      | ( X20
        = ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf('22',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('23',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D_3 ) )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['16','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D_3 ) )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('29',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( X7 != X6 )
      | ( r2_hidden @ X7 @ X8 )
      | ( X8
       != ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('30',plain,(
    ! [X6: $i] :
      ( r2_hidden @ X6 @ ( k1_tarski @ X6 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('32',plain,(
    ! [X6: $i] :
      ( r2_hidden @ X6 @ ( k1_tarski @ X6 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('33',plain,
    ( ( r2_hidden @ sk_B_1 @ k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['34'])).

thf('36',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X8 )
      | ( X9 = X6 )
      | ( X8
       != ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('37',plain,(
    ! [X6: $i,X9: $i] :
      ( ( X9 = X6 )
      | ~ ( r2_hidden @ X9 @ ( k1_tarski @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['34'])).

thf('40',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['34'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k4_xboole_0 @ X2 @ X1 ) ) )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['38','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k4_xboole_0 @ X2 @ X1 ) ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D_3 ) )
      | ( ( k1_tarski @ sk_B_1 )
        = ( k4_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['33','48'])).

thf('50',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_B_1 ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_D_3 ) )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_B_1 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_D_3 ) ) ) ),
    inference('sup-',[status(thm)],['30','51'])).

thf('53',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['28','52'])).

thf('54',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) )
    | ~ ( r2_hidden @ sk_B_1 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( r2_hidden @ sk_B_1 @ k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('56',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference(clc,[status(thm)],['54','55'])).

thf(t172_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) )).

thf('57',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ X30 @ ( k1_relat_1 @ X31 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X31 @ X30 ) @ X32 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v5_relat_1 @ X31 @ X32 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t172_funct_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D_3 )
      | ~ ( v5_relat_1 @ sk_D_3 @ X1 )
      | ~ ( v1_funct_1 @ sk_D_3 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_3 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('60',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( v1_relat_1 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('61',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
    | ( v1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('62',plain,(
    ! [X24: $i,X25: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('63',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v5_relat_1 @ sk_D_3 @ X1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_3 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['58','63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_3 @ X0 ) @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','65'])).

thf('67',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_3 @ sk_C_2 ) @ ( k1_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','66'])).

thf('68',plain,(
    ! [X6: $i,X9: $i] :
      ( ( X9 = X6 )
      | ~ ( r2_hidden @ X9 @ ( k1_tarski @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('69',plain,
    ( ( k1_funct_1 @ sk_D_3 @ sk_C_2 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ( k1_funct_1 @ sk_D_3 @ sk_C_2 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['69','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Vmxy6SJDDP
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:26:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.91/4.12  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.91/4.12  % Solved by: fo/fo7.sh
% 3.91/4.12  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.91/4.12  % done 2756 iterations in 3.669s
% 3.91/4.12  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.91/4.12  % SZS output start Refutation
% 3.91/4.12  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.91/4.12  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.91/4.12  thf(sk_D_3_type, type, sk_D_3: $i).
% 3.91/4.12  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.91/4.12  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 3.91/4.12  thf(sk_B_1_type, type, sk_B_1: $i).
% 3.91/4.12  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.91/4.12  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.91/4.12  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.91/4.12  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 3.91/4.12  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.91/4.12  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.91/4.12  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.91/4.12  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.91/4.12  thf(sk_A_type, type, sk_A: $i).
% 3.91/4.12  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.91/4.12  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.91/4.12  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.91/4.12  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 3.91/4.12  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.91/4.12  thf(sk_C_2_type, type, sk_C_2: $i).
% 3.91/4.12  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.91/4.12  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.91/4.12  thf(t65_funct_2, conjecture,
% 3.91/4.12    (![A:$i,B:$i,C:$i,D:$i]:
% 3.91/4.12     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 3.91/4.12         ( m1_subset_1 @
% 3.91/4.12           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 3.91/4.12       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 3.91/4.12  thf(zf_stmt_0, negated_conjecture,
% 3.91/4.12    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 3.91/4.12        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 3.91/4.12            ( m1_subset_1 @
% 3.91/4.12              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 3.91/4.12          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 3.91/4.12    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 3.91/4.12  thf('0', plain, ((r2_hidden @ sk_C_2 @ sk_A)),
% 3.91/4.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.91/4.12  thf('1', plain,
% 3.91/4.12      ((m1_subset_1 @ sk_D_3 @ 
% 3.91/4.12        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 3.91/4.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.91/4.12  thf(cc2_relset_1, axiom,
% 3.91/4.12    (![A:$i,B:$i,C:$i]:
% 3.91/4.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.91/4.12       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.91/4.12  thf('2', plain,
% 3.91/4.12      (![X33 : $i, X34 : $i, X35 : $i]:
% 3.91/4.12         ((v5_relat_1 @ X33 @ X35)
% 3.91/4.12          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 3.91/4.12      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.91/4.12  thf('3', plain, ((v5_relat_1 @ sk_D_3 @ (k1_tarski @ sk_B_1))),
% 3.91/4.12      inference('sup-', [status(thm)], ['1', '2'])).
% 3.91/4.12  thf(d1_funct_2, axiom,
% 3.91/4.12    (![A:$i,B:$i,C:$i]:
% 3.91/4.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.91/4.12       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.91/4.12           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.91/4.12             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.91/4.12         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.91/4.12           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.91/4.12             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.91/4.12  thf(zf_stmt_1, axiom,
% 3.91/4.12    (![B:$i,A:$i]:
% 3.91/4.12     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.91/4.12       ( zip_tseitin_0 @ B @ A ) ))).
% 3.91/4.12  thf('4', plain,
% 3.91/4.12      (![X41 : $i, X42 : $i]:
% 3.91/4.12         ((zip_tseitin_0 @ X41 @ X42) | ((X41) = (k1_xboole_0)))),
% 3.91/4.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.91/4.12  thf('5', plain,
% 3.91/4.12      ((m1_subset_1 @ sk_D_3 @ 
% 3.91/4.12        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 3.91/4.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.91/4.12  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.91/4.12  thf(zf_stmt_3, axiom,
% 3.91/4.12    (![C:$i,B:$i,A:$i]:
% 3.91/4.12     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.91/4.12       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.91/4.12  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 3.91/4.12  thf(zf_stmt_5, axiom,
% 3.91/4.12    (![A:$i,B:$i,C:$i]:
% 3.91/4.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.91/4.12       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.91/4.12         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.91/4.12           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.91/4.12             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.91/4.12  thf('6', plain,
% 3.91/4.12      (![X46 : $i, X47 : $i, X48 : $i]:
% 3.91/4.12         (~ (zip_tseitin_0 @ X46 @ X47)
% 3.91/4.12          | (zip_tseitin_1 @ X48 @ X46 @ X47)
% 3.91/4.12          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46))))),
% 3.91/4.12      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.91/4.12  thf('7', plain,
% 3.91/4.12      (((zip_tseitin_1 @ sk_D_3 @ (k1_tarski @ sk_B_1) @ sk_A)
% 3.91/4.12        | ~ (zip_tseitin_0 @ (k1_tarski @ sk_B_1) @ sk_A))),
% 3.91/4.12      inference('sup-', [status(thm)], ['5', '6'])).
% 3.91/4.12  thf('8', plain,
% 3.91/4.12      ((((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 3.91/4.12        | (zip_tseitin_1 @ sk_D_3 @ (k1_tarski @ sk_B_1) @ sk_A))),
% 3.91/4.12      inference('sup-', [status(thm)], ['4', '7'])).
% 3.91/4.12  thf('9', plain, ((v1_funct_2 @ sk_D_3 @ sk_A @ (k1_tarski @ sk_B_1))),
% 3.91/4.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.91/4.12  thf('10', plain,
% 3.91/4.12      (![X43 : $i, X44 : $i, X45 : $i]:
% 3.91/4.12         (~ (v1_funct_2 @ X45 @ X43 @ X44)
% 3.91/4.12          | ((X43) = (k1_relset_1 @ X43 @ X44 @ X45))
% 3.91/4.12          | ~ (zip_tseitin_1 @ X45 @ X44 @ X43))),
% 3.91/4.12      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.91/4.12  thf('11', plain,
% 3.91/4.12      ((~ (zip_tseitin_1 @ sk_D_3 @ (k1_tarski @ sk_B_1) @ sk_A)
% 3.91/4.12        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D_3)))),
% 3.91/4.12      inference('sup-', [status(thm)], ['9', '10'])).
% 3.91/4.12  thf('12', plain,
% 3.91/4.12      ((m1_subset_1 @ sk_D_3 @ 
% 3.91/4.12        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 3.91/4.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.91/4.12  thf(redefinition_k1_relset_1, axiom,
% 3.91/4.12    (![A:$i,B:$i,C:$i]:
% 3.91/4.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.91/4.12       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.91/4.12  thf('13', plain,
% 3.91/4.12      (![X36 : $i, X37 : $i, X38 : $i]:
% 3.91/4.12         (((k1_relset_1 @ X37 @ X38 @ X36) = (k1_relat_1 @ X36))
% 3.91/4.12          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 3.91/4.12      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.91/4.12  thf('14', plain,
% 3.91/4.12      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D_3)
% 3.91/4.12         = (k1_relat_1 @ sk_D_3))),
% 3.91/4.12      inference('sup-', [status(thm)], ['12', '13'])).
% 3.91/4.12  thf('15', plain,
% 3.91/4.12      ((~ (zip_tseitin_1 @ sk_D_3 @ (k1_tarski @ sk_B_1) @ sk_A)
% 3.91/4.12        | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 3.91/4.12      inference('demod', [status(thm)], ['11', '14'])).
% 3.91/4.12  thf('16', plain,
% 3.91/4.12      ((((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 3.91/4.12        | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 3.91/4.12      inference('sup-', [status(thm)], ['8', '15'])).
% 3.91/4.12  thf(l44_zfmisc_1, axiom,
% 3.91/4.12    (![A:$i,B:$i]:
% 3.91/4.12     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 3.91/4.12          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 3.91/4.12  thf('17', plain,
% 3.91/4.12      (![X20 : $i, X21 : $i]:
% 3.91/4.12         (((X20) = (k1_xboole_0))
% 3.91/4.12          | (r2_hidden @ (sk_C_1 @ X21 @ X20) @ X20)
% 3.91/4.12          | ((X20) = (k1_tarski @ X21)))),
% 3.91/4.12      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 3.91/4.12  thf(d5_xboole_0, axiom,
% 3.91/4.12    (![A:$i,B:$i,C:$i]:
% 3.91/4.12     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 3.91/4.12       ( ![D:$i]:
% 3.91/4.12         ( ( r2_hidden @ D @ C ) <=>
% 3.91/4.12           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 3.91/4.12  thf('18', plain,
% 3.91/4.12      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 3.91/4.12         (~ (r2_hidden @ X4 @ X3)
% 3.91/4.12          | (r2_hidden @ X4 @ X1)
% 3.91/4.12          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 3.91/4.12      inference('cnf', [status(esa)], [d5_xboole_0])).
% 3.91/4.12  thf('19', plain,
% 3.91/4.12      (![X1 : $i, X2 : $i, X4 : $i]:
% 3.91/4.12         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 3.91/4.12      inference('simplify', [status(thm)], ['18'])).
% 3.91/4.12  thf('20', plain,
% 3.91/4.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.91/4.12         (((k4_xboole_0 @ X1 @ X0) = (k1_tarski @ X2))
% 3.91/4.12          | ((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 3.91/4.12          | (r2_hidden @ (sk_C_1 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 3.91/4.12      inference('sup-', [status(thm)], ['17', '19'])).
% 3.91/4.12  thf('21', plain,
% 3.91/4.12      (![X20 : $i, X21 : $i]:
% 3.91/4.12         (((X20) = (k1_xboole_0))
% 3.91/4.12          | (r2_hidden @ (sk_C_1 @ X21 @ X20) @ X20)
% 3.91/4.12          | ((X20) = (k1_tarski @ X21)))),
% 3.91/4.12      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 3.91/4.12  thf('22', plain,
% 3.91/4.12      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 3.91/4.12         (~ (r2_hidden @ X4 @ X3)
% 3.91/4.12          | ~ (r2_hidden @ X4 @ X2)
% 3.91/4.12          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 3.91/4.12      inference('cnf', [status(esa)], [d5_xboole_0])).
% 3.91/4.12  thf('23', plain,
% 3.91/4.12      (![X1 : $i, X2 : $i, X4 : $i]:
% 3.91/4.12         (~ (r2_hidden @ X4 @ X2)
% 3.91/4.12          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 3.91/4.12      inference('simplify', [status(thm)], ['22'])).
% 3.91/4.12  thf('24', plain,
% 3.91/4.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.91/4.12         (((k4_xboole_0 @ X1 @ X0) = (k1_tarski @ X2))
% 3.91/4.12          | ((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 3.91/4.12          | ~ (r2_hidden @ (sk_C_1 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 3.91/4.12      inference('sup-', [status(thm)], ['21', '23'])).
% 3.91/4.12  thf('25', plain,
% 3.91/4.12      (![X0 : $i, X1 : $i]:
% 3.91/4.12         (((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))
% 3.91/4.12          | ((k4_xboole_0 @ X0 @ X0) = (k1_tarski @ X1))
% 3.91/4.12          | ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))
% 3.91/4.12          | ((k4_xboole_0 @ X0 @ X0) = (k1_tarski @ X1)))),
% 3.91/4.12      inference('sup-', [status(thm)], ['20', '24'])).
% 3.91/4.12  thf('26', plain,
% 3.91/4.12      (![X0 : $i, X1 : $i]:
% 3.91/4.12         (((k4_xboole_0 @ X0 @ X0) = (k1_tarski @ X1))
% 3.91/4.12          | ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0)))),
% 3.91/4.12      inference('simplify', [status(thm)], ['25'])).
% 3.91/4.12  thf('27', plain,
% 3.91/4.12      (![X0 : $i]:
% 3.91/4.12         (((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))
% 3.91/4.12          | ((sk_A) = (k1_relat_1 @ sk_D_3))
% 3.91/4.12          | ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0)))),
% 3.91/4.12      inference('sup+', [status(thm)], ['16', '26'])).
% 3.91/4.12  thf('28', plain,
% 3.91/4.12      (![X0 : $i]:
% 3.91/4.12         (((sk_A) = (k1_relat_1 @ sk_D_3))
% 3.91/4.12          | ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0)))),
% 3.91/4.12      inference('simplify', [status(thm)], ['27'])).
% 3.91/4.12  thf(d1_tarski, axiom,
% 3.91/4.12    (![A:$i,B:$i]:
% 3.91/4.12     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 3.91/4.12       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 3.91/4.12  thf('29', plain,
% 3.91/4.12      (![X6 : $i, X7 : $i, X8 : $i]:
% 3.91/4.12         (((X7) != (X6)) | (r2_hidden @ X7 @ X8) | ((X8) != (k1_tarski @ X6)))),
% 3.91/4.12      inference('cnf', [status(esa)], [d1_tarski])).
% 3.91/4.12  thf('30', plain, (![X6 : $i]: (r2_hidden @ X6 @ (k1_tarski @ X6))),
% 3.91/4.12      inference('simplify', [status(thm)], ['29'])).
% 3.91/4.12  thf('31', plain,
% 3.91/4.12      ((((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 3.91/4.12        | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 3.91/4.12      inference('sup-', [status(thm)], ['8', '15'])).
% 3.91/4.12  thf('32', plain, (![X6 : $i]: (r2_hidden @ X6 @ (k1_tarski @ X6))),
% 3.91/4.12      inference('simplify', [status(thm)], ['29'])).
% 3.91/4.12  thf('33', plain,
% 3.91/4.12      (((r2_hidden @ sk_B_1 @ k1_xboole_0) | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 3.91/4.12      inference('sup+', [status(thm)], ['31', '32'])).
% 3.91/4.12  thf('34', plain,
% 3.91/4.12      (![X1 : $i, X2 : $i, X5 : $i]:
% 3.91/4.12         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 3.91/4.12          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 3.91/4.12          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 3.91/4.12      inference('cnf', [status(esa)], [d5_xboole_0])).
% 3.91/4.12  thf('35', plain,
% 3.91/4.12      (![X0 : $i, X1 : $i]:
% 3.91/4.12         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 3.91/4.12          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 3.91/4.12      inference('eq_fact', [status(thm)], ['34'])).
% 3.91/4.12  thf('36', plain,
% 3.91/4.12      (![X6 : $i, X8 : $i, X9 : $i]:
% 3.91/4.12         (~ (r2_hidden @ X9 @ X8) | ((X9) = (X6)) | ((X8) != (k1_tarski @ X6)))),
% 3.91/4.12      inference('cnf', [status(esa)], [d1_tarski])).
% 3.91/4.12  thf('37', plain,
% 3.91/4.12      (![X6 : $i, X9 : $i]:
% 3.91/4.12         (((X9) = (X6)) | ~ (r2_hidden @ X9 @ (k1_tarski @ X6)))),
% 3.91/4.12      inference('simplify', [status(thm)], ['36'])).
% 3.91/4.12  thf('38', plain,
% 3.91/4.12      (![X0 : $i, X1 : $i]:
% 3.91/4.12         (((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 3.91/4.12          | ((sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 3.91/4.12      inference('sup-', [status(thm)], ['35', '37'])).
% 3.91/4.12  thf('39', plain,
% 3.91/4.12      (![X0 : $i, X1 : $i]:
% 3.91/4.12         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 3.91/4.12          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 3.91/4.12      inference('eq_fact', [status(thm)], ['34'])).
% 3.91/4.12  thf('40', plain,
% 3.91/4.12      (![X1 : $i, X2 : $i, X5 : $i]:
% 3.91/4.12         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 3.91/4.12          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 3.91/4.12          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 3.91/4.12          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 3.91/4.12      inference('cnf', [status(esa)], [d5_xboole_0])).
% 3.91/4.12  thf('41', plain,
% 3.91/4.12      (![X0 : $i, X1 : $i]:
% 3.91/4.12         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 3.91/4.12          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 3.91/4.12          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 3.91/4.12          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 3.91/4.12      inference('sup-', [status(thm)], ['39', '40'])).
% 3.91/4.12  thf('42', plain,
% 3.91/4.12      (![X0 : $i, X1 : $i]:
% 3.91/4.12         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 3.91/4.12          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 3.91/4.12          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 3.91/4.12      inference('simplify', [status(thm)], ['41'])).
% 3.91/4.12  thf('43', plain,
% 3.91/4.12      (![X0 : $i, X1 : $i]:
% 3.91/4.12         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 3.91/4.12          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 3.91/4.12      inference('eq_fact', [status(thm)], ['34'])).
% 3.91/4.12  thf('44', plain,
% 3.91/4.12      (![X0 : $i, X1 : $i]:
% 3.91/4.12         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 3.91/4.12          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 3.91/4.12      inference('clc', [status(thm)], ['42', '43'])).
% 3.91/4.12  thf('45', plain,
% 3.91/4.12      (![X1 : $i, X2 : $i, X4 : $i]:
% 3.91/4.12         (~ (r2_hidden @ X4 @ X2)
% 3.91/4.12          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 3.91/4.12      inference('simplify', [status(thm)], ['22'])).
% 3.91/4.12  thf('46', plain,
% 3.91/4.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.91/4.12         (((X2) = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 3.91/4.12          | ~ (r2_hidden @ (sk_D @ X2 @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X0))),
% 3.91/4.12      inference('sup-', [status(thm)], ['44', '45'])).
% 3.91/4.12  thf('47', plain,
% 3.91/4.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.91/4.12         (~ (r2_hidden @ X0 @ X1)
% 3.91/4.12          | ((k1_tarski @ X0)
% 3.91/4.12              = (k4_xboole_0 @ (k1_tarski @ X0) @ (k4_xboole_0 @ X2 @ X1)))
% 3.91/4.12          | ((k1_tarski @ X0)
% 3.91/4.12              = (k4_xboole_0 @ (k1_tarski @ X0) @ (k4_xboole_0 @ X2 @ X1))))),
% 3.91/4.12      inference('sup-', [status(thm)], ['38', '46'])).
% 3.91/4.12  thf('48', plain,
% 3.91/4.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.91/4.12         (((k1_tarski @ X0)
% 3.91/4.12            = (k4_xboole_0 @ (k1_tarski @ X0) @ (k4_xboole_0 @ X2 @ X1)))
% 3.91/4.12          | ~ (r2_hidden @ X0 @ X1))),
% 3.91/4.12      inference('simplify', [status(thm)], ['47'])).
% 3.91/4.12  thf('49', plain,
% 3.91/4.12      (![X0 : $i]:
% 3.91/4.12         (((sk_A) = (k1_relat_1 @ sk_D_3))
% 3.91/4.12          | ((k1_tarski @ sk_B_1)
% 3.91/4.12              = (k4_xboole_0 @ (k1_tarski @ sk_B_1) @ 
% 3.91/4.12                 (k4_xboole_0 @ X0 @ k1_xboole_0))))),
% 3.91/4.12      inference('sup-', [status(thm)], ['33', '48'])).
% 3.91/4.12  thf('50', plain,
% 3.91/4.12      (![X1 : $i, X2 : $i, X4 : $i]:
% 3.91/4.12         (~ (r2_hidden @ X4 @ X2)
% 3.91/4.12          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 3.91/4.12      inference('simplify', [status(thm)], ['22'])).
% 3.91/4.12  thf('51', plain,
% 3.91/4.12      (![X0 : $i, X1 : $i]:
% 3.91/4.12         (~ (r2_hidden @ X1 @ (k1_tarski @ sk_B_1))
% 3.91/4.12          | ((sk_A) = (k1_relat_1 @ sk_D_3))
% 3.91/4.12          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 3.91/4.12      inference('sup-', [status(thm)], ['49', '50'])).
% 3.91/4.12  thf('52', plain,
% 3.91/4.12      (![X0 : $i]:
% 3.91/4.12         (~ (r2_hidden @ sk_B_1 @ (k4_xboole_0 @ X0 @ k1_xboole_0))
% 3.91/4.12          | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 3.91/4.12      inference('sup-', [status(thm)], ['30', '51'])).
% 3.91/4.12  thf('53', plain,
% 3.91/4.12      ((~ (r2_hidden @ sk_B_1 @ k1_xboole_0)
% 3.91/4.12        | ((sk_A) = (k1_relat_1 @ sk_D_3))
% 3.91/4.12        | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 3.91/4.12      inference('sup-', [status(thm)], ['28', '52'])).
% 3.91/4.12  thf('54', plain,
% 3.91/4.12      ((((sk_A) = (k1_relat_1 @ sk_D_3)) | ~ (r2_hidden @ sk_B_1 @ k1_xboole_0))),
% 3.91/4.12      inference('simplify', [status(thm)], ['53'])).
% 3.91/4.12  thf('55', plain,
% 3.91/4.12      (((r2_hidden @ sk_B_1 @ k1_xboole_0) | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 3.91/4.12      inference('sup+', [status(thm)], ['31', '32'])).
% 3.91/4.12  thf('56', plain, (((sk_A) = (k1_relat_1 @ sk_D_3))),
% 3.91/4.12      inference('clc', [status(thm)], ['54', '55'])).
% 3.91/4.12  thf(t172_funct_1, axiom,
% 3.91/4.12    (![A:$i,B:$i]:
% 3.91/4.12     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 3.91/4.12       ( ![C:$i]:
% 3.91/4.12         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 3.91/4.12           ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) ))).
% 3.91/4.12  thf('57', plain,
% 3.91/4.12      (![X30 : $i, X31 : $i, X32 : $i]:
% 3.91/4.12         (~ (r2_hidden @ X30 @ (k1_relat_1 @ X31))
% 3.91/4.12          | (r2_hidden @ (k1_funct_1 @ X31 @ X30) @ X32)
% 3.91/4.12          | ~ (v1_funct_1 @ X31)
% 3.91/4.12          | ~ (v5_relat_1 @ X31 @ X32)
% 3.91/4.12          | ~ (v1_relat_1 @ X31))),
% 3.91/4.12      inference('cnf', [status(esa)], [t172_funct_1])).
% 3.91/4.12  thf('58', plain,
% 3.91/4.12      (![X0 : $i, X1 : $i]:
% 3.91/4.12         (~ (r2_hidden @ X0 @ sk_A)
% 3.91/4.12          | ~ (v1_relat_1 @ sk_D_3)
% 3.91/4.12          | ~ (v5_relat_1 @ sk_D_3 @ X1)
% 3.91/4.12          | ~ (v1_funct_1 @ sk_D_3)
% 3.91/4.12          | (r2_hidden @ (k1_funct_1 @ sk_D_3 @ X0) @ X1))),
% 3.91/4.12      inference('sup-', [status(thm)], ['56', '57'])).
% 3.91/4.12  thf('59', plain,
% 3.91/4.12      ((m1_subset_1 @ sk_D_3 @ 
% 3.91/4.12        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 3.91/4.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.91/4.12  thf(cc2_relat_1, axiom,
% 3.91/4.12    (![A:$i]:
% 3.91/4.12     ( ( v1_relat_1 @ A ) =>
% 3.91/4.12       ( ![B:$i]:
% 3.91/4.12         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 3.91/4.12  thf('60', plain,
% 3.91/4.12      (![X22 : $i, X23 : $i]:
% 3.91/4.12         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 3.91/4.12          | (v1_relat_1 @ X22)
% 3.91/4.12          | ~ (v1_relat_1 @ X23))),
% 3.91/4.12      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.91/4.12  thf('61', plain,
% 3.91/4.12      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1)))
% 3.91/4.12        | (v1_relat_1 @ sk_D_3))),
% 3.91/4.12      inference('sup-', [status(thm)], ['59', '60'])).
% 3.91/4.12  thf(fc6_relat_1, axiom,
% 3.91/4.12    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 3.91/4.12  thf('62', plain,
% 3.91/4.12      (![X24 : $i, X25 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X24 @ X25))),
% 3.91/4.12      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.91/4.12  thf('63', plain, ((v1_relat_1 @ sk_D_3)),
% 3.91/4.12      inference('demod', [status(thm)], ['61', '62'])).
% 3.91/4.12  thf('64', plain, ((v1_funct_1 @ sk_D_3)),
% 3.91/4.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.91/4.12  thf('65', plain,
% 3.91/4.12      (![X0 : $i, X1 : $i]:
% 3.91/4.12         (~ (r2_hidden @ X0 @ sk_A)
% 3.91/4.12          | ~ (v5_relat_1 @ sk_D_3 @ X1)
% 3.91/4.12          | (r2_hidden @ (k1_funct_1 @ sk_D_3 @ X0) @ X1))),
% 3.91/4.12      inference('demod', [status(thm)], ['58', '63', '64'])).
% 3.91/4.12  thf('66', plain,
% 3.91/4.12      (![X0 : $i]:
% 3.91/4.12         ((r2_hidden @ (k1_funct_1 @ sk_D_3 @ X0) @ (k1_tarski @ sk_B_1))
% 3.91/4.12          | ~ (r2_hidden @ X0 @ sk_A))),
% 3.91/4.12      inference('sup-', [status(thm)], ['3', '65'])).
% 3.91/4.12  thf('67', plain,
% 3.91/4.12      ((r2_hidden @ (k1_funct_1 @ sk_D_3 @ sk_C_2) @ (k1_tarski @ sk_B_1))),
% 3.91/4.12      inference('sup-', [status(thm)], ['0', '66'])).
% 3.91/4.12  thf('68', plain,
% 3.91/4.12      (![X6 : $i, X9 : $i]:
% 3.91/4.12         (((X9) = (X6)) | ~ (r2_hidden @ X9 @ (k1_tarski @ X6)))),
% 3.91/4.12      inference('simplify', [status(thm)], ['36'])).
% 3.91/4.12  thf('69', plain, (((k1_funct_1 @ sk_D_3 @ sk_C_2) = (sk_B_1))),
% 3.91/4.12      inference('sup-', [status(thm)], ['67', '68'])).
% 3.91/4.12  thf('70', plain, (((k1_funct_1 @ sk_D_3 @ sk_C_2) != (sk_B_1))),
% 3.91/4.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.91/4.12  thf('71', plain, ($false),
% 3.91/4.12      inference('simplify_reflect-', [status(thm)], ['69', '70'])).
% 3.91/4.12  
% 3.91/4.12  % SZS output end Refutation
% 3.91/4.12  
% 3.95/4.13  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
