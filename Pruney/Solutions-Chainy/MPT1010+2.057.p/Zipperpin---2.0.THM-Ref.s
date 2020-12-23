%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GI3M2X797G

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:21 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 116 expanded)
%              Number of leaves         :   41 (  53 expanded)
%              Depth                    :   15
%              Number of atoms          :  597 ( 998 expanded)
%              Number of equality atoms :   33 (  55 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
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

thf('2',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ( X41
        = ( k1_relset_1 @ X41 @ X42 @ X43 ) )
      | ~ ( zip_tseitin_1 @ X43 @ X42 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('5',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('6',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('7',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ~ ( r1_tarski @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
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

thf('12',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( zip_tseitin_0 @ X44 @ X45 )
      | ( zip_tseitin_1 @ X46 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('13',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ~ ( zip_tseitin_0 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( zip_tseitin_1 @ sk_D_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('15',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( X5 != X4 )
      | ( r2_hidden @ X5 @ X6 )
      | ( X6
       != ( k1_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('16',plain,(
    ! [X4: $i] :
      ( r2_hidden @ X4 @ ( k1_tarski @ X4 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    zip_tseitin_1 @ sk_D_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['14','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k1_relset_1 @ X34 @ X35 @ X33 )
        = ( k1_relat_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['3','19','22'])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('24',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X23 @ ( k1_relat_1 @ X24 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X24 @ X23 ) @ ( k2_relat_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D_1 )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ ( k2_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('27',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v1_relat_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('28',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ ( k2_relat_1 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['25','28','29'])).

thf('31',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['0','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('33',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X30 @ X31 @ X32 ) @ ( k1_zfmisc_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('34',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('36',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k2_relset_1 @ X37 @ X38 @ X36 )
        = ( k2_relat_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('37',plain,
    ( ( k2_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['34','37'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('39',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( m1_subset_1 @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_D_1 @ sk_C_1 ) @ ( k1_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['31','40'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('42',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r2_hidden @ X18 @ X19 )
      | ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_C_1 ) @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('45',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_C_1 ) @ ( k1_tarski @ sk_B_1 ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( X7 = X4 )
      | ( X6
       != ( k1_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('47',plain,(
    ! [X4: $i,X7: $i] :
      ( ( X7 = X4 )
      | ~ ( r2_hidden @ X7 @ ( k1_tarski @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( k1_funct_1 @ sk_D_1 @ sk_C_1 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    ( k1_funct_1 @ sk_D_1 @ sk_C_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['48','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GI3M2X797G
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:49:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.42/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.59  % Solved by: fo/fo7.sh
% 0.42/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.59  % done 153 iterations in 0.135s
% 0.42/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.59  % SZS output start Refutation
% 0.42/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.42/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.42/0.59  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.42/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.42/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.42/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.42/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.59  thf(sk_B_type, type, sk_B: $i > $i).
% 0.42/0.59  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.42/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.42/0.59  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.42/0.59  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.42/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.42/0.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.42/0.59  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.42/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.42/0.59  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.42/0.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.42/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.59  thf(t65_funct_2, conjecture,
% 0.42/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.59     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.42/0.59         ( m1_subset_1 @
% 0.42/0.59           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.42/0.59       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.42/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.59    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.59        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.42/0.59            ( m1_subset_1 @
% 0.42/0.59              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.42/0.59          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.42/0.59    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.42/0.59  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('1', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf(d1_funct_2, axiom,
% 0.42/0.59    (![A:$i,B:$i,C:$i]:
% 0.42/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.59       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.42/0.59           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.42/0.59             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.42/0.59         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.59           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.42/0.59             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.42/0.59  thf(zf_stmt_1, axiom,
% 0.42/0.59    (![C:$i,B:$i,A:$i]:
% 0.42/0.59     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.42/0.59       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.42/0.59  thf('2', plain,
% 0.42/0.59      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.42/0.59         (~ (v1_funct_2 @ X43 @ X41 @ X42)
% 0.42/0.59          | ((X41) = (k1_relset_1 @ X41 @ X42 @ X43))
% 0.42/0.59          | ~ (zip_tseitin_1 @ X43 @ X42 @ X41))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.59  thf('3', plain,
% 0.42/0.59      ((~ (zip_tseitin_1 @ sk_D_1 @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.42/0.59        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D_1)))),
% 0.42/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.42/0.59  thf(zf_stmt_2, axiom,
% 0.42/0.59    (![B:$i,A:$i]:
% 0.42/0.59     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.59       ( zip_tseitin_0 @ B @ A ) ))).
% 0.42/0.59  thf('4', plain,
% 0.42/0.59      (![X39 : $i, X40 : $i]:
% 0.42/0.59         ((zip_tseitin_0 @ X39 @ X40) | ((X39) = (k1_xboole_0)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.42/0.59  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.42/0.59  thf('5', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.42/0.59      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.42/0.59  thf(d1_xboole_0, axiom,
% 0.42/0.59    (![A:$i]:
% 0.42/0.59     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.42/0.59  thf('6', plain,
% 0.42/0.59      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.42/0.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.42/0.59  thf(t7_ordinal1, axiom,
% 0.42/0.59    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.42/0.59  thf('7', plain,
% 0.42/0.59      (![X25 : $i, X26 : $i]:
% 0.42/0.59         (~ (r2_hidden @ X25 @ X26) | ~ (r1_tarski @ X26 @ X25))),
% 0.42/0.59      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.42/0.59  thf('8', plain,
% 0.42/0.59      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.42/0.59      inference('sup-', [status(thm)], ['6', '7'])).
% 0.42/0.59  thf('9', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.42/0.59      inference('sup-', [status(thm)], ['5', '8'])).
% 0.42/0.59  thf('10', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.42/0.59      inference('sup+', [status(thm)], ['4', '9'])).
% 0.42/0.59  thf('11', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_D_1 @ 
% 0.42/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.42/0.59  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.42/0.59  thf(zf_stmt_5, axiom,
% 0.42/0.59    (![A:$i,B:$i,C:$i]:
% 0.42/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.59       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.42/0.59         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.42/0.59           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.42/0.59             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.42/0.59  thf('12', plain,
% 0.42/0.59      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.42/0.59         (~ (zip_tseitin_0 @ X44 @ X45)
% 0.42/0.59          | (zip_tseitin_1 @ X46 @ X44 @ X45)
% 0.42/0.59          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44))))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.42/0.59  thf('13', plain,
% 0.42/0.59      (((zip_tseitin_1 @ sk_D_1 @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.42/0.59        | ~ (zip_tseitin_0 @ (k1_tarski @ sk_B_1) @ sk_A))),
% 0.42/0.59      inference('sup-', [status(thm)], ['11', '12'])).
% 0.42/0.59  thf('14', plain,
% 0.42/0.59      (((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.42/0.59        | (zip_tseitin_1 @ sk_D_1 @ (k1_tarski @ sk_B_1) @ sk_A))),
% 0.42/0.59      inference('sup-', [status(thm)], ['10', '13'])).
% 0.42/0.59  thf(d1_tarski, axiom,
% 0.42/0.59    (![A:$i,B:$i]:
% 0.42/0.59     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.42/0.59       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.42/0.59  thf('15', plain,
% 0.42/0.59      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.42/0.59         (((X5) != (X4)) | (r2_hidden @ X5 @ X6) | ((X6) != (k1_tarski @ X4)))),
% 0.42/0.59      inference('cnf', [status(esa)], [d1_tarski])).
% 0.42/0.59  thf('16', plain, (![X4 : $i]: (r2_hidden @ X4 @ (k1_tarski @ X4))),
% 0.42/0.59      inference('simplify', [status(thm)], ['15'])).
% 0.42/0.59  thf('17', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.42/0.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.42/0.59  thf('18', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.42/0.59      inference('sup-', [status(thm)], ['16', '17'])).
% 0.42/0.59  thf('19', plain, ((zip_tseitin_1 @ sk_D_1 @ (k1_tarski @ sk_B_1) @ sk_A)),
% 0.42/0.59      inference('clc', [status(thm)], ['14', '18'])).
% 0.42/0.59  thf('20', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_D_1 @ 
% 0.42/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf(redefinition_k1_relset_1, axiom,
% 0.42/0.59    (![A:$i,B:$i,C:$i]:
% 0.42/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.59       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.42/0.59  thf('21', plain,
% 0.42/0.59      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.42/0.59         (((k1_relset_1 @ X34 @ X35 @ X33) = (k1_relat_1 @ X33))
% 0.42/0.59          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.42/0.59      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.42/0.59  thf('22', plain,
% 0.42/0.59      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D_1)
% 0.42/0.59         = (k1_relat_1 @ sk_D_1))),
% 0.42/0.59      inference('sup-', [status(thm)], ['20', '21'])).
% 0.42/0.59  thf('23', plain, (((sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.42/0.59      inference('demod', [status(thm)], ['3', '19', '22'])).
% 0.42/0.59  thf(t12_funct_1, axiom,
% 0.42/0.59    (![A:$i,B:$i]:
% 0.42/0.59     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.42/0.59       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.42/0.59         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.42/0.59  thf('24', plain,
% 0.42/0.59      (![X23 : $i, X24 : $i]:
% 0.42/0.59         (~ (r2_hidden @ X23 @ (k1_relat_1 @ X24))
% 0.42/0.59          | (r2_hidden @ (k1_funct_1 @ X24 @ X23) @ (k2_relat_1 @ X24))
% 0.42/0.59          | ~ (v1_funct_1 @ X24)
% 0.42/0.59          | ~ (v1_relat_1 @ X24))),
% 0.42/0.59      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.42/0.59  thf('25', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         (~ (r2_hidden @ X0 @ sk_A)
% 0.42/0.59          | ~ (v1_relat_1 @ sk_D_1)
% 0.42/0.59          | ~ (v1_funct_1 @ sk_D_1)
% 0.42/0.59          | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ (k2_relat_1 @ sk_D_1)))),
% 0.42/0.59      inference('sup-', [status(thm)], ['23', '24'])).
% 0.42/0.59  thf('26', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_D_1 @ 
% 0.42/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf(cc1_relset_1, axiom,
% 0.42/0.59    (![A:$i,B:$i,C:$i]:
% 0.42/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.59       ( v1_relat_1 @ C ) ))).
% 0.42/0.59  thf('27', plain,
% 0.42/0.59      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.42/0.59         ((v1_relat_1 @ X27)
% 0.42/0.59          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.42/0.59      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.42/0.59  thf('28', plain, ((v1_relat_1 @ sk_D_1)),
% 0.42/0.59      inference('sup-', [status(thm)], ['26', '27'])).
% 0.42/0.59  thf('29', plain, ((v1_funct_1 @ sk_D_1)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('30', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         (~ (r2_hidden @ X0 @ sk_A)
% 0.42/0.59          | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ (k2_relat_1 @ sk_D_1)))),
% 0.42/0.59      inference('demod', [status(thm)], ['25', '28', '29'])).
% 0.42/0.59  thf('31', plain,
% 0.42/0.59      ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_C_1) @ (k2_relat_1 @ sk_D_1))),
% 0.42/0.59      inference('sup-', [status(thm)], ['0', '30'])).
% 0.42/0.59  thf('32', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_D_1 @ 
% 0.42/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf(dt_k2_relset_1, axiom,
% 0.42/0.59    (![A:$i,B:$i,C:$i]:
% 0.42/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.59       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.42/0.59  thf('33', plain,
% 0.42/0.59      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.42/0.59         ((m1_subset_1 @ (k2_relset_1 @ X30 @ X31 @ X32) @ (k1_zfmisc_1 @ X31))
% 0.42/0.59          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.42/0.59      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.42/0.59  thf('34', plain,
% 0.42/0.59      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D_1) @ 
% 0.42/0.59        (k1_zfmisc_1 @ (k1_tarski @ sk_B_1)))),
% 0.42/0.59      inference('sup-', [status(thm)], ['32', '33'])).
% 0.42/0.59  thf('35', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_D_1 @ 
% 0.42/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf(redefinition_k2_relset_1, axiom,
% 0.42/0.59    (![A:$i,B:$i,C:$i]:
% 0.42/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.59       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.42/0.59  thf('36', plain,
% 0.42/0.59      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.42/0.59         (((k2_relset_1 @ X37 @ X38 @ X36) = (k2_relat_1 @ X36))
% 0.42/0.59          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 0.42/0.59      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.42/0.59  thf('37', plain,
% 0.42/0.59      (((k2_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D_1)
% 0.42/0.59         = (k2_relat_1 @ sk_D_1))),
% 0.42/0.59      inference('sup-', [status(thm)], ['35', '36'])).
% 0.42/0.59  thf('38', plain,
% 0.42/0.59      ((m1_subset_1 @ (k2_relat_1 @ sk_D_1) @ 
% 0.42/0.59        (k1_zfmisc_1 @ (k1_tarski @ sk_B_1)))),
% 0.42/0.59      inference('demod', [status(thm)], ['34', '37'])).
% 0.42/0.59  thf(t4_subset, axiom,
% 0.42/0.59    (![A:$i,B:$i,C:$i]:
% 0.42/0.59     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.42/0.59       ( m1_subset_1 @ A @ C ) ))).
% 0.42/0.59  thf('39', plain,
% 0.42/0.59      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.42/0.59         (~ (r2_hidden @ X20 @ X21)
% 0.42/0.59          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 0.42/0.59          | (m1_subset_1 @ X20 @ X22))),
% 0.42/0.59      inference('cnf', [status(esa)], [t4_subset])).
% 0.42/0.59  thf('40', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         ((m1_subset_1 @ X0 @ (k1_tarski @ sk_B_1))
% 0.42/0.59          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_1)))),
% 0.42/0.59      inference('sup-', [status(thm)], ['38', '39'])).
% 0.42/0.59  thf('41', plain,
% 0.42/0.59      ((m1_subset_1 @ (k1_funct_1 @ sk_D_1 @ sk_C_1) @ (k1_tarski @ sk_B_1))),
% 0.42/0.59      inference('sup-', [status(thm)], ['31', '40'])).
% 0.42/0.59  thf(t2_subset, axiom,
% 0.42/0.59    (![A:$i,B:$i]:
% 0.42/0.59     ( ( m1_subset_1 @ A @ B ) =>
% 0.42/0.59       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.42/0.59  thf('42', plain,
% 0.42/0.59      (![X18 : $i, X19 : $i]:
% 0.42/0.59         ((r2_hidden @ X18 @ X19)
% 0.42/0.59          | (v1_xboole_0 @ X19)
% 0.42/0.59          | ~ (m1_subset_1 @ X18 @ X19))),
% 0.42/0.59      inference('cnf', [status(esa)], [t2_subset])).
% 0.42/0.59  thf('43', plain,
% 0.42/0.59      (((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.42/0.59        | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_C_1) @ (k1_tarski @ sk_B_1)))),
% 0.42/0.59      inference('sup-', [status(thm)], ['41', '42'])).
% 0.42/0.59  thf('44', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.42/0.59      inference('sup-', [status(thm)], ['16', '17'])).
% 0.42/0.59  thf('45', plain,
% 0.42/0.59      ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_C_1) @ (k1_tarski @ sk_B_1))),
% 0.42/0.59      inference('clc', [status(thm)], ['43', '44'])).
% 0.42/0.59  thf('46', plain,
% 0.42/0.59      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.42/0.59         (~ (r2_hidden @ X7 @ X6) | ((X7) = (X4)) | ((X6) != (k1_tarski @ X4)))),
% 0.42/0.59      inference('cnf', [status(esa)], [d1_tarski])).
% 0.42/0.59  thf('47', plain,
% 0.42/0.59      (![X4 : $i, X7 : $i]:
% 0.42/0.59         (((X7) = (X4)) | ~ (r2_hidden @ X7 @ (k1_tarski @ X4)))),
% 0.42/0.59      inference('simplify', [status(thm)], ['46'])).
% 0.42/0.59  thf('48', plain, (((k1_funct_1 @ sk_D_1 @ sk_C_1) = (sk_B_1))),
% 0.42/0.59      inference('sup-', [status(thm)], ['45', '47'])).
% 0.42/0.59  thf('49', plain, (((k1_funct_1 @ sk_D_1 @ sk_C_1) != (sk_B_1))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('50', plain, ($false),
% 0.42/0.59      inference('simplify_reflect-', [status(thm)], ['48', '49'])).
% 0.42/0.59  
% 0.42/0.59  % SZS output end Refutation
% 0.42/0.59  
% 0.42/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
