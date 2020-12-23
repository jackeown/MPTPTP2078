%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ERFqxHfrdP

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:27 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 112 expanded)
%              Number of leaves         :   41 (  51 expanded)
%              Depth                    :   14
%              Number of atoms          :  600 ( 982 expanded)
%              Number of equality atoms :   33 (  55 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

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
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
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
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( v1_funct_2 @ X50 @ X48 @ X49 )
      | ( X48
        = ( k1_relset_1 @ X48 @ X49 @ X50 ) )
      | ~ ( zip_tseitin_2 @ X50 @ X49 @ X48 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
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
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( zip_tseitin_1 @ X51 @ X52 )
      | ( zip_tseitin_2 @ X53 @ X51 @ X52 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X51 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ~ ( zip_tseitin_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X46: $i,X47: $i] :
      ( ( zip_tseitin_1 @ X46 @ X47 )
      | ( X46 = k1_xboole_0 ) ) ),
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
    ! [X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X35 @ X36 )
      | ~ ( r1_tarski @ X36 @ X35 ) ) ),
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
    zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['6','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('17',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( ( k1_relset_1 @ X41 @ X42 @ X40 )
        = ( k1_relat_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('18',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','15','18'])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('20',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X33 @ ( k1_relat_1 @ X34 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X34 @ X33 ) @ ( k2_relat_1 @ X34 ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('23',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) )
      | ( v1_relat_1 @ X29 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('25',plain,(
    ! [X31: $i,X32: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('26',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['21','26','27'])).

thf('29',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['0','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('31',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X37 @ X38 @ X39 ) @ ( k1_zfmisc_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('32',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('34',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( ( k2_relset_1 @ X44 @ X45 @ X43 )
        = ( k2_relat_1 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('35',plain,
    ( ( k2_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['32','35'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('37',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) )
      | ( m1_subset_1 @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ ( k1_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['29','38'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('40',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r2_hidden @ X24 @ X25 )
      | ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('41',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X16: $i] :
      ( r2_hidden @ X16 @ ( k1_tarski @ X16 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ ( k1_tarski @ sk_B_1 ) ),
    inference(clc,[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X18 )
      | ( X19 = X16 )
      | ( X18
       != ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('47',plain,(
    ! [X16: $i,X19: $i] :
      ( ( X19 = X16 )
      | ~ ( r2_hidden @ X19 @ ( k1_tarski @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( k1_funct_1 @ sk_D @ sk_C_1 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    ( k1_funct_1 @ sk_D @ sk_C_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['48','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ERFqxHfrdP
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:36:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.56  % Solved by: fo/fo7.sh
% 0.35/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.56  % done 137 iterations in 0.103s
% 0.35/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.56  % SZS output start Refutation
% 0.35/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.35/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.35/0.56  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.35/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.35/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.56  thf(sk_D_type, type, sk_D: $i).
% 0.35/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.35/0.56  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.35/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.35/0.56  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.35/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.35/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.56  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.35/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.35/0.56  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.35/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.56  thf(t65_funct_2, conjecture,
% 0.35/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.56     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.35/0.56         ( m1_subset_1 @
% 0.35/0.56           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.35/0.56       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.35/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.56    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.56        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.35/0.56            ( m1_subset_1 @
% 0.35/0.56              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.35/0.56          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.35/0.56    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.35/0.56  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('1', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf(d1_funct_2, axiom,
% 0.35/0.56    (![A:$i,B:$i,C:$i]:
% 0.35/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.56       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.35/0.56           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.35/0.56             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.35/0.56         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.35/0.56           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.35/0.56             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.35/0.56  thf(zf_stmt_1, axiom,
% 0.35/0.56    (![C:$i,B:$i,A:$i]:
% 0.35/0.56     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.35/0.56       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.35/0.56  thf('2', plain,
% 0.35/0.56      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.35/0.56         (~ (v1_funct_2 @ X50 @ X48 @ X49)
% 0.35/0.56          | ((X48) = (k1_relset_1 @ X48 @ X49 @ X50))
% 0.35/0.56          | ~ (zip_tseitin_2 @ X50 @ X49 @ X48))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.35/0.56  thf('3', plain,
% 0.35/0.56      ((~ (zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.35/0.56        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D)))),
% 0.35/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.35/0.56  thf('4', plain,
% 0.35/0.56      ((m1_subset_1 @ sk_D @ 
% 0.35/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.35/0.56  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $o).
% 0.35/0.56  thf(zf_stmt_4, axiom,
% 0.35/0.56    (![B:$i,A:$i]:
% 0.35/0.56     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.35/0.56       ( zip_tseitin_1 @ B @ A ) ))).
% 0.35/0.56  thf(zf_stmt_5, axiom,
% 0.35/0.56    (![A:$i,B:$i,C:$i]:
% 0.35/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.56       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.35/0.56         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.35/0.56           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.35/0.56             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.35/0.56  thf('5', plain,
% 0.35/0.56      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.35/0.56         (~ (zip_tseitin_1 @ X51 @ X52)
% 0.35/0.56          | (zip_tseitin_2 @ X53 @ X51 @ X52)
% 0.35/0.56          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X51))))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.35/0.56  thf('6', plain,
% 0.35/0.56      (((zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.35/0.56        | ~ (zip_tseitin_1 @ (k1_tarski @ sk_B_1) @ sk_A))),
% 0.35/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.35/0.56  thf('7', plain,
% 0.35/0.56      (![X46 : $i, X47 : $i]:
% 0.35/0.56         ((zip_tseitin_1 @ X46 @ X47) | ((X46) = (k1_xboole_0)))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.35/0.56  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.35/0.56  thf('8', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.35/0.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.35/0.56  thf('9', plain,
% 0.35/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.56         ((r1_tarski @ X0 @ X1) | (zip_tseitin_1 @ X0 @ X2))),
% 0.35/0.56      inference('sup+', [status(thm)], ['7', '8'])).
% 0.35/0.56  thf(d1_tarski, axiom,
% 0.35/0.56    (![A:$i,B:$i]:
% 0.35/0.56     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.35/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.35/0.56  thf('10', plain,
% 0.35/0.56      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.35/0.56         (((X17) != (X16))
% 0.35/0.56          | (r2_hidden @ X17 @ X18)
% 0.35/0.56          | ((X18) != (k1_tarski @ X16)))),
% 0.35/0.56      inference('cnf', [status(esa)], [d1_tarski])).
% 0.35/0.56  thf('11', plain, (![X16 : $i]: (r2_hidden @ X16 @ (k1_tarski @ X16))),
% 0.35/0.56      inference('simplify', [status(thm)], ['10'])).
% 0.35/0.56  thf(t7_ordinal1, axiom,
% 0.35/0.56    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.35/0.56  thf('12', plain,
% 0.35/0.56      (![X35 : $i, X36 : $i]:
% 0.35/0.56         (~ (r2_hidden @ X35 @ X36) | ~ (r1_tarski @ X36 @ X35))),
% 0.35/0.56      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.35/0.56  thf('13', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_tarski @ X0) @ X0)),
% 0.35/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.35/0.56  thf('14', plain,
% 0.35/0.56      (![X0 : $i, X1 : $i]: (zip_tseitin_1 @ (k1_tarski @ X0) @ X1)),
% 0.35/0.56      inference('sup-', [status(thm)], ['9', '13'])).
% 0.35/0.56  thf('15', plain, ((zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B_1) @ sk_A)),
% 0.35/0.56      inference('demod', [status(thm)], ['6', '14'])).
% 0.35/0.56  thf('16', plain,
% 0.35/0.56      ((m1_subset_1 @ sk_D @ 
% 0.35/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf(redefinition_k1_relset_1, axiom,
% 0.35/0.56    (![A:$i,B:$i,C:$i]:
% 0.35/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.56       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.35/0.56  thf('17', plain,
% 0.35/0.56      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.35/0.56         (((k1_relset_1 @ X41 @ X42 @ X40) = (k1_relat_1 @ X40))
% 0.35/0.56          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42))))),
% 0.35/0.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.35/0.56  thf('18', plain,
% 0.35/0.56      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D)
% 0.35/0.56         = (k1_relat_1 @ sk_D))),
% 0.35/0.56      inference('sup-', [status(thm)], ['16', '17'])).
% 0.35/0.56  thf('19', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.35/0.56      inference('demod', [status(thm)], ['3', '15', '18'])).
% 0.35/0.56  thf(t12_funct_1, axiom,
% 0.35/0.56    (![A:$i,B:$i]:
% 0.35/0.56     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.35/0.56       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.35/0.56         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.35/0.56  thf('20', plain,
% 0.35/0.56      (![X33 : $i, X34 : $i]:
% 0.35/0.56         (~ (r2_hidden @ X33 @ (k1_relat_1 @ X34))
% 0.35/0.56          | (r2_hidden @ (k1_funct_1 @ X34 @ X33) @ (k2_relat_1 @ X34))
% 0.35/0.56          | ~ (v1_funct_1 @ X34)
% 0.35/0.56          | ~ (v1_relat_1 @ X34))),
% 0.35/0.56      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.35/0.56  thf('21', plain,
% 0.35/0.56      (![X0 : $i]:
% 0.35/0.56         (~ (r2_hidden @ X0 @ sk_A)
% 0.35/0.56          | ~ (v1_relat_1 @ sk_D)
% 0.35/0.56          | ~ (v1_funct_1 @ sk_D)
% 0.35/0.56          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D)))),
% 0.35/0.56      inference('sup-', [status(thm)], ['19', '20'])).
% 0.35/0.56  thf('22', plain,
% 0.35/0.56      ((m1_subset_1 @ sk_D @ 
% 0.35/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf(cc2_relat_1, axiom,
% 0.35/0.56    (![A:$i]:
% 0.35/0.56     ( ( v1_relat_1 @ A ) =>
% 0.35/0.56       ( ![B:$i]:
% 0.35/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.35/0.56  thf('23', plain,
% 0.35/0.56      (![X29 : $i, X30 : $i]:
% 0.35/0.56         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30))
% 0.35/0.56          | (v1_relat_1 @ X29)
% 0.35/0.56          | ~ (v1_relat_1 @ X30))),
% 0.35/0.56      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.35/0.56  thf('24', plain,
% 0.35/0.56      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.35/0.56        | (v1_relat_1 @ sk_D))),
% 0.35/0.56      inference('sup-', [status(thm)], ['22', '23'])).
% 0.35/0.56  thf(fc6_relat_1, axiom,
% 0.35/0.56    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.35/0.56  thf('25', plain,
% 0.35/0.56      (![X31 : $i, X32 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X31 @ X32))),
% 0.35/0.56      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.35/0.56  thf('26', plain, ((v1_relat_1 @ sk_D)),
% 0.35/0.56      inference('demod', [status(thm)], ['24', '25'])).
% 0.35/0.56  thf('27', plain, ((v1_funct_1 @ sk_D)),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('28', plain,
% 0.35/0.56      (![X0 : $i]:
% 0.35/0.56         (~ (r2_hidden @ X0 @ sk_A)
% 0.35/0.56          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D)))),
% 0.35/0.56      inference('demod', [status(thm)], ['21', '26', '27'])).
% 0.35/0.56  thf('29', plain,
% 0.35/0.56      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_C_1) @ (k2_relat_1 @ sk_D))),
% 0.35/0.56      inference('sup-', [status(thm)], ['0', '28'])).
% 0.35/0.56  thf('30', plain,
% 0.35/0.56      ((m1_subset_1 @ sk_D @ 
% 0.35/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf(dt_k2_relset_1, axiom,
% 0.35/0.56    (![A:$i,B:$i,C:$i]:
% 0.35/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.56       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.35/0.56  thf('31', plain,
% 0.35/0.56      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.35/0.56         ((m1_subset_1 @ (k2_relset_1 @ X37 @ X38 @ X39) @ (k1_zfmisc_1 @ X38))
% 0.35/0.56          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 0.35/0.56      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.35/0.56  thf('32', plain,
% 0.35/0.56      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D) @ 
% 0.35/0.56        (k1_zfmisc_1 @ (k1_tarski @ sk_B_1)))),
% 0.35/0.56      inference('sup-', [status(thm)], ['30', '31'])).
% 0.35/0.56  thf('33', plain,
% 0.35/0.56      ((m1_subset_1 @ sk_D @ 
% 0.35/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf(redefinition_k2_relset_1, axiom,
% 0.35/0.56    (![A:$i,B:$i,C:$i]:
% 0.35/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.56       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.35/0.56  thf('34', plain,
% 0.35/0.56      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.35/0.56         (((k2_relset_1 @ X44 @ X45 @ X43) = (k2_relat_1 @ X43))
% 0.35/0.56          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45))))),
% 0.35/0.56      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.35/0.56  thf('35', plain,
% 0.35/0.56      (((k2_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D)
% 0.35/0.56         = (k2_relat_1 @ sk_D))),
% 0.35/0.56      inference('sup-', [status(thm)], ['33', '34'])).
% 0.35/0.56  thf('36', plain,
% 0.35/0.56      ((m1_subset_1 @ (k2_relat_1 @ sk_D) @ 
% 0.35/0.56        (k1_zfmisc_1 @ (k1_tarski @ sk_B_1)))),
% 0.35/0.56      inference('demod', [status(thm)], ['32', '35'])).
% 0.35/0.56  thf(t4_subset, axiom,
% 0.35/0.56    (![A:$i,B:$i,C:$i]:
% 0.35/0.56     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.35/0.56       ( m1_subset_1 @ A @ C ) ))).
% 0.35/0.56  thf('37', plain,
% 0.35/0.56      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.35/0.56         (~ (r2_hidden @ X26 @ X27)
% 0.35/0.56          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28))
% 0.35/0.56          | (m1_subset_1 @ X26 @ X28))),
% 0.35/0.56      inference('cnf', [status(esa)], [t4_subset])).
% 0.35/0.56  thf('38', plain,
% 0.35/0.56      (![X0 : $i]:
% 0.35/0.56         ((m1_subset_1 @ X0 @ (k1_tarski @ sk_B_1))
% 0.35/0.56          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D)))),
% 0.35/0.56      inference('sup-', [status(thm)], ['36', '37'])).
% 0.35/0.56  thf('39', plain,
% 0.35/0.56      ((m1_subset_1 @ (k1_funct_1 @ sk_D @ sk_C_1) @ (k1_tarski @ sk_B_1))),
% 0.35/0.56      inference('sup-', [status(thm)], ['29', '38'])).
% 0.35/0.56  thf(t2_subset, axiom,
% 0.35/0.56    (![A:$i,B:$i]:
% 0.35/0.56     ( ( m1_subset_1 @ A @ B ) =>
% 0.35/0.56       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.35/0.56  thf('40', plain,
% 0.35/0.56      (![X24 : $i, X25 : $i]:
% 0.35/0.56         ((r2_hidden @ X24 @ X25)
% 0.35/0.56          | (v1_xboole_0 @ X25)
% 0.35/0.56          | ~ (m1_subset_1 @ X24 @ X25))),
% 0.35/0.56      inference('cnf', [status(esa)], [t2_subset])).
% 0.35/0.56  thf('41', plain,
% 0.35/0.56      (((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.35/0.56        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C_1) @ (k1_tarski @ sk_B_1)))),
% 0.35/0.56      inference('sup-', [status(thm)], ['39', '40'])).
% 0.35/0.56  thf('42', plain, (![X16 : $i]: (r2_hidden @ X16 @ (k1_tarski @ X16))),
% 0.35/0.56      inference('simplify', [status(thm)], ['10'])).
% 0.35/0.56  thf(d1_xboole_0, axiom,
% 0.35/0.56    (![A:$i]:
% 0.35/0.56     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.35/0.56  thf('43', plain,
% 0.35/0.56      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.35/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.35/0.56  thf('44', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.35/0.56      inference('sup-', [status(thm)], ['42', '43'])).
% 0.35/0.56  thf('45', plain,
% 0.35/0.56      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_C_1) @ (k1_tarski @ sk_B_1))),
% 0.35/0.56      inference('clc', [status(thm)], ['41', '44'])).
% 0.35/0.56  thf('46', plain,
% 0.35/0.56      (![X16 : $i, X18 : $i, X19 : $i]:
% 0.35/0.56         (~ (r2_hidden @ X19 @ X18)
% 0.35/0.56          | ((X19) = (X16))
% 0.35/0.56          | ((X18) != (k1_tarski @ X16)))),
% 0.35/0.56      inference('cnf', [status(esa)], [d1_tarski])).
% 0.35/0.56  thf('47', plain,
% 0.35/0.56      (![X16 : $i, X19 : $i]:
% 0.35/0.56         (((X19) = (X16)) | ~ (r2_hidden @ X19 @ (k1_tarski @ X16)))),
% 0.35/0.56      inference('simplify', [status(thm)], ['46'])).
% 0.35/0.56  thf('48', plain, (((k1_funct_1 @ sk_D @ sk_C_1) = (sk_B_1))),
% 0.35/0.56      inference('sup-', [status(thm)], ['45', '47'])).
% 0.35/0.56  thf('49', plain, (((k1_funct_1 @ sk_D @ sk_C_1) != (sk_B_1))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('50', plain, ($false),
% 0.35/0.56      inference('simplify_reflect-', [status(thm)], ['48', '49'])).
% 0.35/0.56  
% 0.35/0.56  % SZS output end Refutation
% 0.35/0.56  
% 0.35/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
