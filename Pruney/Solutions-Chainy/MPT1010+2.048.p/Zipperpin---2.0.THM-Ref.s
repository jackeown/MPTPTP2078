%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1wnNbAkCX9

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:19 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 110 expanded)
%              Number of leaves         :   40 (  50 expanded)
%              Depth                    :   14
%              Number of atoms          :  611 ( 993 expanded)
%              Number of equality atoms :   37 (  59 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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
    v1_funct_2 @ sk_D_2 @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
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
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('2',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ~ ( v1_funct_2 @ X57 @ X55 @ X56 )
      | ( X55
        = ( k1_relset_1 @ X55 @ X56 @ X57 ) )
      | ~ ( zip_tseitin_2 @ X57 @ X56 @ X55 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_2 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_1 @ B @ A )
         => ( zip_tseitin_2 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ~ ( zip_tseitin_1 @ X58 @ X59 )
      | ( zip_tseitin_2 @ X60 @ X58 @ X59 )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X58 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_2 @ sk_D_2 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ~ ( zip_tseitin_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X53: $i,X54: $i] :
      ( ( zip_tseitin_1 @ X53 @ X54 )
      | ( X53 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('8',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('10',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( X17 != X16 )
      | ( r2_hidden @ X17 @ X18 )
      | ( X18
       != ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('11',plain,(
    ! [X16: $i] :
      ( r2_hidden @ X16 @ ( k1_tarski @ X16 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('12',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ X39 @ X40 )
      | ~ ( r1_tarski @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('13',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( zip_tseitin_1 @ ( k1_tarski @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,(
    zip_tseitin_2 @ sk_D_2 @ ( k1_tarski @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['6','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('17',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( ( k1_relset_1 @ X48 @ X49 @ X47 )
        = ( k1_relat_1 @ X47 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('18',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['3','15','18'])).

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

thf('20',plain,(
    ! [X33: $i,X35: $i,X37: $i,X38: $i] :
      ( ( X35
       != ( k2_relat_1 @ X33 ) )
      | ( r2_hidden @ X37 @ X35 )
      | ~ ( r2_hidden @ X38 @ ( k1_relat_1 @ X33 ) )
      | ( X37
       != ( k1_funct_1 @ X33 @ X38 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('21',plain,(
    ! [X33: $i,X38: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( r2_hidden @ X38 @ ( k1_relat_1 @ X33 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X33 @ X38 ) @ ( k2_relat_1 @ X33 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k2_relat_1 @ sk_D_2 ) )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ~ ( v1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('25',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( v1_relat_1 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('26',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['22','23','26'])).

thf('28',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_2 ) @ ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['0','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('30',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X44 @ X45 @ X46 ) @ ( k1_zfmisc_1 @ X45 ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('31',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D_2 ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('33',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( ( k2_relset_1 @ X51 @ X52 @ X50 )
        = ( k2_relat_1 @ X50 ) )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('34',plain,
    ( ( k2_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['31','34'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('36',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) )
      | ( m1_subset_1 @ X29 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_D_2 @ sk_C_2 ) @ ( k1_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['28','37'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('39',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r2_hidden @ X27 @ X28 )
      | ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_2 ) @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X16: $i] :
      ( r2_hidden @ X16 @ ( k1_tarski @ X16 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_2 ) @ ( k1_tarski @ sk_B_1 ) ),
    inference(clc,[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X18 )
      | ( X19 = X16 )
      | ( X18
       != ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('46',plain,(
    ! [X16: $i,X19: $i] :
      ( ( X19 = X16 )
      | ~ ( r2_hidden @ X19 @ ( k1_tarski @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( k1_funct_1 @ sk_D_2 @ sk_C_2 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,(
    ( k1_funct_1 @ sk_D_2 @ sk_C_2 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['47','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1wnNbAkCX9
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:08:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.66  % Solved by: fo/fo7.sh
% 0.45/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.66  % done 248 iterations in 0.207s
% 0.45/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.66  % SZS output start Refutation
% 0.45/0.66  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.45/0.66  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.45/0.66  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.66  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.45/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.66  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.66  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.45/0.66  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.45/0.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.66  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.66  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.45/0.66  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.66  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.45/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.66  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.45/0.66  thf(t65_funct_2, conjecture,
% 0.45/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.66     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.45/0.66         ( m1_subset_1 @
% 0.45/0.66           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.45/0.66       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.45/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.66    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.66        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.45/0.66            ( m1_subset_1 @
% 0.45/0.66              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.45/0.66          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.45/0.66    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.45/0.66  thf('0', plain, ((r2_hidden @ sk_C_2 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('1', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(d1_funct_2, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.66       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.66           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.45/0.66             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.45/0.66         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.66           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.45/0.66             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.45/0.66  thf(zf_stmt_1, axiom,
% 0.45/0.66    (![C:$i,B:$i,A:$i]:
% 0.45/0.66     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.45/0.66       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.45/0.66  thf('2', plain,
% 0.45/0.66      (![X55 : $i, X56 : $i, X57 : $i]:
% 0.45/0.66         (~ (v1_funct_2 @ X57 @ X55 @ X56)
% 0.45/0.66          | ((X55) = (k1_relset_1 @ X55 @ X56 @ X57))
% 0.45/0.66          | ~ (zip_tseitin_2 @ X57 @ X56 @ X55))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.45/0.66  thf('3', plain,
% 0.45/0.66      ((~ (zip_tseitin_2 @ sk_D_2 @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.45/0.66        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D_2)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.66  thf('4', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_D_2 @ 
% 0.45/0.66        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.45/0.66  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $o).
% 0.45/0.66  thf(zf_stmt_4, axiom,
% 0.45/0.66    (![B:$i,A:$i]:
% 0.45/0.66     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.66       ( zip_tseitin_1 @ B @ A ) ))).
% 0.45/0.66  thf(zf_stmt_5, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.66       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.45/0.66         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.66           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.45/0.66             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.45/0.66  thf('5', plain,
% 0.45/0.66      (![X58 : $i, X59 : $i, X60 : $i]:
% 0.45/0.66         (~ (zip_tseitin_1 @ X58 @ X59)
% 0.45/0.66          | (zip_tseitin_2 @ X60 @ X58 @ X59)
% 0.45/0.66          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X58))))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.45/0.66  thf('6', plain,
% 0.45/0.66      (((zip_tseitin_2 @ sk_D_2 @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.45/0.66        | ~ (zip_tseitin_1 @ (k1_tarski @ sk_B_1) @ sk_A))),
% 0.45/0.66      inference('sup-', [status(thm)], ['4', '5'])).
% 0.45/0.66  thf('7', plain,
% 0.45/0.66      (![X53 : $i, X54 : $i]:
% 0.45/0.66         ((zip_tseitin_1 @ X53 @ X54) | ((X53) = (k1_xboole_0)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.45/0.66  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.45/0.66  thf('8', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.45/0.66      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.66  thf('9', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.66         ((r1_tarski @ X0 @ X1) | (zip_tseitin_1 @ X0 @ X2))),
% 0.45/0.66      inference('sup+', [status(thm)], ['7', '8'])).
% 0.45/0.66  thf(d1_tarski, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.45/0.66       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.45/0.66  thf('10', plain,
% 0.45/0.66      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.45/0.66         (((X17) != (X16))
% 0.45/0.66          | (r2_hidden @ X17 @ X18)
% 0.45/0.66          | ((X18) != (k1_tarski @ X16)))),
% 0.45/0.66      inference('cnf', [status(esa)], [d1_tarski])).
% 0.45/0.66  thf('11', plain, (![X16 : $i]: (r2_hidden @ X16 @ (k1_tarski @ X16))),
% 0.45/0.66      inference('simplify', [status(thm)], ['10'])).
% 0.45/0.66  thf(t7_ordinal1, axiom,
% 0.45/0.66    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.66  thf('12', plain,
% 0.45/0.66      (![X39 : $i, X40 : $i]:
% 0.45/0.66         (~ (r2_hidden @ X39 @ X40) | ~ (r1_tarski @ X40 @ X39))),
% 0.45/0.66      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.45/0.66  thf('13', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_tarski @ X0) @ X0)),
% 0.45/0.66      inference('sup-', [status(thm)], ['11', '12'])).
% 0.45/0.66  thf('14', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]: (zip_tseitin_1 @ (k1_tarski @ X0) @ X1)),
% 0.45/0.66      inference('sup-', [status(thm)], ['9', '13'])).
% 0.45/0.66  thf('15', plain, ((zip_tseitin_2 @ sk_D_2 @ (k1_tarski @ sk_B_1) @ sk_A)),
% 0.45/0.66      inference('demod', [status(thm)], ['6', '14'])).
% 0.45/0.66  thf('16', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_D_2 @ 
% 0.45/0.66        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(redefinition_k1_relset_1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.66       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.45/0.66  thf('17', plain,
% 0.45/0.66      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.45/0.66         (((k1_relset_1 @ X48 @ X49 @ X47) = (k1_relat_1 @ X47))
% 0.45/0.66          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49))))),
% 0.45/0.66      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.45/0.66  thf('18', plain,
% 0.45/0.66      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D_2)
% 0.45/0.66         = (k1_relat_1 @ sk_D_2))),
% 0.45/0.66      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.66  thf('19', plain, (((sk_A) = (k1_relat_1 @ sk_D_2))),
% 0.45/0.66      inference('demod', [status(thm)], ['3', '15', '18'])).
% 0.45/0.66  thf(d5_funct_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.45/0.66           ( ![C:$i]:
% 0.45/0.66             ( ( r2_hidden @ C @ B ) <=>
% 0.45/0.66               ( ?[D:$i]:
% 0.45/0.66                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.45/0.66                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.45/0.66  thf('20', plain,
% 0.45/0.66      (![X33 : $i, X35 : $i, X37 : $i, X38 : $i]:
% 0.45/0.66         (((X35) != (k2_relat_1 @ X33))
% 0.45/0.66          | (r2_hidden @ X37 @ X35)
% 0.45/0.66          | ~ (r2_hidden @ X38 @ (k1_relat_1 @ X33))
% 0.45/0.66          | ((X37) != (k1_funct_1 @ X33 @ X38))
% 0.45/0.66          | ~ (v1_funct_1 @ X33)
% 0.45/0.66          | ~ (v1_relat_1 @ X33))),
% 0.45/0.66      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.45/0.66  thf('21', plain,
% 0.45/0.66      (![X33 : $i, X38 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X33)
% 0.45/0.66          | ~ (v1_funct_1 @ X33)
% 0.45/0.66          | ~ (r2_hidden @ X38 @ (k1_relat_1 @ X33))
% 0.45/0.66          | (r2_hidden @ (k1_funct_1 @ X33 @ X38) @ (k2_relat_1 @ X33)))),
% 0.45/0.66      inference('simplify', [status(thm)], ['20'])).
% 0.45/0.66  thf('22', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (r2_hidden @ X0 @ sk_A)
% 0.45/0.66          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2))
% 0.45/0.66          | ~ (v1_funct_1 @ sk_D_2)
% 0.45/0.66          | ~ (v1_relat_1 @ sk_D_2))),
% 0.45/0.66      inference('sup-', [status(thm)], ['19', '21'])).
% 0.45/0.66  thf('23', plain, ((v1_funct_1 @ sk_D_2)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('24', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_D_2 @ 
% 0.45/0.66        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(cc1_relset_1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.66       ( v1_relat_1 @ C ) ))).
% 0.45/0.66  thf('25', plain,
% 0.45/0.66      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.45/0.66         ((v1_relat_1 @ X41)
% 0.45/0.66          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43))))),
% 0.45/0.66      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.45/0.66  thf('26', plain, ((v1_relat_1 @ sk_D_2)),
% 0.45/0.66      inference('sup-', [status(thm)], ['24', '25'])).
% 0.45/0.66  thf('27', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (r2_hidden @ X0 @ sk_A)
% 0.45/0.66          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2)))),
% 0.45/0.66      inference('demod', [status(thm)], ['22', '23', '26'])).
% 0.45/0.66  thf('28', plain,
% 0.45/0.66      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_2) @ (k2_relat_1 @ sk_D_2))),
% 0.45/0.66      inference('sup-', [status(thm)], ['0', '27'])).
% 0.45/0.66  thf('29', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_D_2 @ 
% 0.45/0.66        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(dt_k2_relset_1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.66       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.45/0.66  thf('30', plain,
% 0.45/0.66      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.45/0.66         ((m1_subset_1 @ (k2_relset_1 @ X44 @ X45 @ X46) @ (k1_zfmisc_1 @ X45))
% 0.45/0.66          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45))))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.45/0.66  thf('31', plain,
% 0.45/0.66      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D_2) @ 
% 0.45/0.66        (k1_zfmisc_1 @ (k1_tarski @ sk_B_1)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['29', '30'])).
% 0.45/0.66  thf('32', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_D_2 @ 
% 0.45/0.66        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(redefinition_k2_relset_1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.66       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.45/0.66  thf('33', plain,
% 0.45/0.66      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.45/0.66         (((k2_relset_1 @ X51 @ X52 @ X50) = (k2_relat_1 @ X50))
% 0.45/0.66          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52))))),
% 0.45/0.66      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.66  thf('34', plain,
% 0.45/0.66      (((k2_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D_2)
% 0.45/0.66         = (k2_relat_1 @ sk_D_2))),
% 0.45/0.66      inference('sup-', [status(thm)], ['32', '33'])).
% 0.45/0.66  thf('35', plain,
% 0.45/0.66      ((m1_subset_1 @ (k2_relat_1 @ sk_D_2) @ 
% 0.45/0.66        (k1_zfmisc_1 @ (k1_tarski @ sk_B_1)))),
% 0.45/0.66      inference('demod', [status(thm)], ['31', '34'])).
% 0.45/0.66  thf(t4_subset, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.45/0.66       ( m1_subset_1 @ A @ C ) ))).
% 0.45/0.66  thf('36', plain,
% 0.45/0.66      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.45/0.66         (~ (r2_hidden @ X29 @ X30)
% 0.45/0.66          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31))
% 0.45/0.66          | (m1_subset_1 @ X29 @ X31))),
% 0.45/0.66      inference('cnf', [status(esa)], [t4_subset])).
% 0.45/0.66  thf('37', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         ((m1_subset_1 @ X0 @ (k1_tarski @ sk_B_1))
% 0.45/0.66          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_2)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['35', '36'])).
% 0.45/0.66  thf('38', plain,
% 0.45/0.66      ((m1_subset_1 @ (k1_funct_1 @ sk_D_2 @ sk_C_2) @ (k1_tarski @ sk_B_1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['28', '37'])).
% 0.45/0.66  thf(t2_subset, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( m1_subset_1 @ A @ B ) =>
% 0.45/0.66       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.45/0.66  thf('39', plain,
% 0.45/0.66      (![X27 : $i, X28 : $i]:
% 0.45/0.66         ((r2_hidden @ X27 @ X28)
% 0.45/0.66          | (v1_xboole_0 @ X28)
% 0.45/0.66          | ~ (m1_subset_1 @ X27 @ X28))),
% 0.45/0.66      inference('cnf', [status(esa)], [t2_subset])).
% 0.45/0.66  thf('40', plain,
% 0.45/0.66      (((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.45/0.66        | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_2) @ (k1_tarski @ sk_B_1)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['38', '39'])).
% 0.45/0.66  thf('41', plain, (![X16 : $i]: (r2_hidden @ X16 @ (k1_tarski @ X16))),
% 0.45/0.66      inference('simplify', [status(thm)], ['10'])).
% 0.45/0.66  thf(d1_xboole_0, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.45/0.66  thf('42', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.45/0.66      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.66  thf('43', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['41', '42'])).
% 0.45/0.66  thf('44', plain,
% 0.45/0.66      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_2) @ (k1_tarski @ sk_B_1))),
% 0.45/0.66      inference('clc', [status(thm)], ['40', '43'])).
% 0.45/0.66  thf('45', plain,
% 0.45/0.66      (![X16 : $i, X18 : $i, X19 : $i]:
% 0.45/0.66         (~ (r2_hidden @ X19 @ X18)
% 0.45/0.66          | ((X19) = (X16))
% 0.45/0.66          | ((X18) != (k1_tarski @ X16)))),
% 0.45/0.66      inference('cnf', [status(esa)], [d1_tarski])).
% 0.45/0.66  thf('46', plain,
% 0.45/0.66      (![X16 : $i, X19 : $i]:
% 0.45/0.66         (((X19) = (X16)) | ~ (r2_hidden @ X19 @ (k1_tarski @ X16)))),
% 0.45/0.66      inference('simplify', [status(thm)], ['45'])).
% 0.45/0.66  thf('47', plain, (((k1_funct_1 @ sk_D_2 @ sk_C_2) = (sk_B_1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['44', '46'])).
% 0.45/0.66  thf('48', plain, (((k1_funct_1 @ sk_D_2 @ sk_C_2) != (sk_B_1))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('49', plain, ($false),
% 0.45/0.66      inference('simplify_reflect-', [status(thm)], ['47', '48'])).
% 0.45/0.66  
% 0.45/0.66  % SZS output end Refutation
% 0.45/0.66  
% 0.48/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
