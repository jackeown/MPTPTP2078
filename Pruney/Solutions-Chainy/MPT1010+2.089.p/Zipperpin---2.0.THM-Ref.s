%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.04eNaT3UQ6

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:25 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 108 expanded)
%              Number of leaves         :   39 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :  525 ( 925 expanded)
%              Number of equality atoms :   30 (  48 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ),
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
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( v1_funct_2 @ X48 @ X46 @ X47 )
      | ( X46
        = ( k1_relset_1 @ X46 @ X47 @ X48 ) )
      | ~ ( zip_tseitin_2 @ X48 @ X47 @ X46 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
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
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( zip_tseitin_1 @ X49 @ X50 )
      | ( zip_tseitin_2 @ X51 @ X49 @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X49 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_1 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X44: $i,X45: $i] :
      ( ( zip_tseitin_1 @ X44 @ X45 )
      | ( X44 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('8',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( X18 != X17 )
      | ( r2_hidden @ X18 @ X19 )
      | ( X19
       != ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('11',plain,(
    ! [X17: $i] :
      ( r2_hidden @ X17 @ ( k1_tarski @ X17 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('12',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X36 @ X37 )
      | ~ ( r1_tarski @ X37 @ X36 ) ) ),
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
    zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['6','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('17',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( ( k1_relset_1 @ X42 @ X43 @ X41 )
        = ( k1_relat_1 @ X41 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('18',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D )
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
    ! [X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ X34 @ ( k1_relat_1 @ X35 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X35 @ X34 ) @ ( k2_relat_1 @ X35 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('23',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ( v1_relat_1 @ X28 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('25',plain,(
    ! [X32: $i,X33: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ),
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
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C_2 ) @ ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['0','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('31',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( v5_relat_1 @ X38 @ X40 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('32',plain,(
    v5_relat_1 @ sk_D @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('33',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v5_relat_1 @ X30 @ X31 )
      | ( r1_tarski @ ( k2_relat_1 @ X30 ) @ X31 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['24','25'])).

thf('36',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C_2 ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['29','38'])).

thf('40',plain,(
    ! [X17: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X20 @ X19 )
      | ( X20 = X17 )
      | ( X19
       != ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('41',plain,(
    ! [X17: $i,X20: $i] :
      ( ( X20 = X17 )
      | ~ ( r2_hidden @ X20 @ ( k1_tarski @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( k1_funct_1 @ sk_D @ sk_C_2 )
    = sk_B ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    ( k1_funct_1 @ sk_D @ sk_C_2 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['42','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.04eNaT3UQ6
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:59:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.41/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.61  % Solved by: fo/fo7.sh
% 0.41/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.61  % done 183 iterations in 0.174s
% 0.41/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.61  % SZS output start Refutation
% 0.41/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.61  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.41/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.41/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.41/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.61  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.41/0.61  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.41/0.61  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.41/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.61  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.41/0.61  thf(sk_D_type, type, sk_D: $i).
% 0.41/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.41/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.61  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.41/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.41/0.61  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.41/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.41/0.61  thf(t65_funct_2, conjecture,
% 0.41/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.61     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.41/0.61         ( m1_subset_1 @
% 0.41/0.61           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.41/0.61       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.41/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.61    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.61        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.41/0.61            ( m1_subset_1 @
% 0.41/0.61              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.41/0.61          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.41/0.61    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.41/0.61  thf('0', plain, ((r2_hidden @ sk_C_2 @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('1', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(d1_funct_2, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.61       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.41/0.61           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.41/0.61             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.41/0.61         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.41/0.61           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.41/0.61             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.41/0.61  thf(zf_stmt_1, axiom,
% 0.41/0.61    (![C:$i,B:$i,A:$i]:
% 0.41/0.61     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.41/0.61       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.41/0.61  thf('2', plain,
% 0.41/0.61      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.41/0.61         (~ (v1_funct_2 @ X48 @ X46 @ X47)
% 0.41/0.61          | ((X46) = (k1_relset_1 @ X46 @ X47 @ X48))
% 0.41/0.61          | ~ (zip_tseitin_2 @ X48 @ X47 @ X46))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.41/0.61  thf('3', plain,
% 0.41/0.61      ((~ (zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 0.41/0.61        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.41/0.61  thf('4', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_D @ 
% 0.41/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.41/0.61  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $o).
% 0.41/0.61  thf(zf_stmt_4, axiom,
% 0.41/0.61    (![B:$i,A:$i]:
% 0.41/0.61     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.41/0.61       ( zip_tseitin_1 @ B @ A ) ))).
% 0.41/0.61  thf(zf_stmt_5, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.61       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.41/0.61         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.41/0.61           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.41/0.61             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.41/0.61  thf('5', plain,
% 0.41/0.61      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.41/0.61         (~ (zip_tseitin_1 @ X49 @ X50)
% 0.41/0.61          | (zip_tseitin_2 @ X51 @ X49 @ X50)
% 0.41/0.61          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X49))))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.41/0.61  thf('6', plain,
% 0.41/0.61      (((zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 0.41/0.61        | ~ (zip_tseitin_1 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.41/0.61      inference('sup-', [status(thm)], ['4', '5'])).
% 0.41/0.61  thf('7', plain,
% 0.41/0.61      (![X44 : $i, X45 : $i]:
% 0.41/0.61         ((zip_tseitin_1 @ X44 @ X45) | ((X44) = (k1_xboole_0)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.41/0.61  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.41/0.61  thf('8', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.41/0.61      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.41/0.61  thf('9', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.61         ((r1_tarski @ X0 @ X1) | (zip_tseitin_1 @ X0 @ X2))),
% 0.41/0.61      inference('sup+', [status(thm)], ['7', '8'])).
% 0.41/0.61  thf(d1_tarski, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.41/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.41/0.61  thf('10', plain,
% 0.41/0.61      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.41/0.61         (((X18) != (X17))
% 0.41/0.61          | (r2_hidden @ X18 @ X19)
% 0.41/0.61          | ((X19) != (k1_tarski @ X17)))),
% 0.41/0.61      inference('cnf', [status(esa)], [d1_tarski])).
% 0.41/0.61  thf('11', plain, (![X17 : $i]: (r2_hidden @ X17 @ (k1_tarski @ X17))),
% 0.41/0.61      inference('simplify', [status(thm)], ['10'])).
% 0.41/0.61  thf(t7_ordinal1, axiom,
% 0.41/0.61    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.41/0.61  thf('12', plain,
% 0.41/0.61      (![X36 : $i, X37 : $i]:
% 0.41/0.61         (~ (r2_hidden @ X36 @ X37) | ~ (r1_tarski @ X37 @ X36))),
% 0.41/0.61      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.41/0.61  thf('13', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_tarski @ X0) @ X0)),
% 0.41/0.61      inference('sup-', [status(thm)], ['11', '12'])).
% 0.41/0.61  thf('14', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]: (zip_tseitin_1 @ (k1_tarski @ X0) @ X1)),
% 0.41/0.61      inference('sup-', [status(thm)], ['9', '13'])).
% 0.41/0.61  thf('15', plain, ((zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)),
% 0.41/0.61      inference('demod', [status(thm)], ['6', '14'])).
% 0.41/0.61  thf('16', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_D @ 
% 0.41/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(redefinition_k1_relset_1, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.61       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.41/0.61  thf('17', plain,
% 0.41/0.61      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.41/0.61         (((k1_relset_1 @ X42 @ X43 @ X41) = (k1_relat_1 @ X41))
% 0.41/0.61          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43))))),
% 0.41/0.61      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.41/0.61  thf('18', plain,
% 0.41/0.61      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.41/0.61      inference('sup-', [status(thm)], ['16', '17'])).
% 0.41/0.61  thf('19', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.41/0.61      inference('demod', [status(thm)], ['3', '15', '18'])).
% 0.41/0.61  thf(t12_funct_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.41/0.61       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.41/0.61         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.41/0.61  thf('20', plain,
% 0.41/0.61      (![X34 : $i, X35 : $i]:
% 0.41/0.61         (~ (r2_hidden @ X34 @ (k1_relat_1 @ X35))
% 0.41/0.61          | (r2_hidden @ (k1_funct_1 @ X35 @ X34) @ (k2_relat_1 @ X35))
% 0.41/0.61          | ~ (v1_funct_1 @ X35)
% 0.41/0.61          | ~ (v1_relat_1 @ X35))),
% 0.41/0.61      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.41/0.61  thf('21', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (r2_hidden @ X0 @ sk_A)
% 0.41/0.61          | ~ (v1_relat_1 @ sk_D)
% 0.41/0.61          | ~ (v1_funct_1 @ sk_D)
% 0.41/0.61          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['19', '20'])).
% 0.41/0.61  thf('22', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_D @ 
% 0.41/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(cc2_relat_1, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( v1_relat_1 @ A ) =>
% 0.41/0.61       ( ![B:$i]:
% 0.41/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.41/0.61  thf('23', plain,
% 0.41/0.61      (![X28 : $i, X29 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 0.41/0.61          | (v1_relat_1 @ X28)
% 0.41/0.61          | ~ (v1_relat_1 @ X29))),
% 0.41/0.61      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.41/0.61  thf('24', plain,
% 0.41/0.61      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))
% 0.41/0.61        | (v1_relat_1 @ sk_D))),
% 0.41/0.61      inference('sup-', [status(thm)], ['22', '23'])).
% 0.41/0.61  thf(fc6_relat_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.41/0.61  thf('25', plain,
% 0.41/0.61      (![X32 : $i, X33 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X32 @ X33))),
% 0.41/0.61      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.41/0.61  thf('26', plain, ((v1_relat_1 @ sk_D)),
% 0.41/0.61      inference('demod', [status(thm)], ['24', '25'])).
% 0.41/0.61  thf('27', plain, ((v1_funct_1 @ sk_D)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('28', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (r2_hidden @ X0 @ sk_A)
% 0.41/0.61          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D)))),
% 0.41/0.61      inference('demod', [status(thm)], ['21', '26', '27'])).
% 0.41/0.61  thf('29', plain,
% 0.41/0.61      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_C_2) @ (k2_relat_1 @ sk_D))),
% 0.41/0.61      inference('sup-', [status(thm)], ['0', '28'])).
% 0.41/0.61  thf('30', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_D @ 
% 0.41/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(cc2_relset_1, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.61       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.41/0.61  thf('31', plain,
% 0.41/0.61      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.41/0.61         ((v5_relat_1 @ X38 @ X40)
% 0.41/0.61          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40))))),
% 0.41/0.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.41/0.61  thf('32', plain, ((v5_relat_1 @ sk_D @ (k1_tarski @ sk_B))),
% 0.41/0.61      inference('sup-', [status(thm)], ['30', '31'])).
% 0.41/0.61  thf(d19_relat_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( v1_relat_1 @ B ) =>
% 0.41/0.61       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.41/0.61  thf('33', plain,
% 0.41/0.61      (![X30 : $i, X31 : $i]:
% 0.41/0.61         (~ (v5_relat_1 @ X30 @ X31)
% 0.41/0.61          | (r1_tarski @ (k2_relat_1 @ X30) @ X31)
% 0.41/0.61          | ~ (v1_relat_1 @ X30))),
% 0.41/0.61      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.41/0.61  thf('34', plain,
% 0.41/0.61      ((~ (v1_relat_1 @ sk_D)
% 0.41/0.61        | (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_tarski @ sk_B)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['32', '33'])).
% 0.41/0.61  thf('35', plain, ((v1_relat_1 @ sk_D)),
% 0.41/0.61      inference('demod', [status(thm)], ['24', '25'])).
% 0.41/0.61  thf('36', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_tarski @ sk_B))),
% 0.41/0.61      inference('demod', [status(thm)], ['34', '35'])).
% 0.41/0.61  thf(d3_tarski, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( r1_tarski @ A @ B ) <=>
% 0.41/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.41/0.61  thf('37', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.61         (~ (r2_hidden @ X0 @ X1)
% 0.41/0.61          | (r2_hidden @ X0 @ X2)
% 0.41/0.61          | ~ (r1_tarski @ X1 @ X2))),
% 0.41/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.61  thf('38', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.41/0.61          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['36', '37'])).
% 0.41/0.61  thf('39', plain,
% 0.41/0.61      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_C_2) @ (k1_tarski @ sk_B))),
% 0.41/0.61      inference('sup-', [status(thm)], ['29', '38'])).
% 0.41/0.61  thf('40', plain,
% 0.41/0.61      (![X17 : $i, X19 : $i, X20 : $i]:
% 0.41/0.61         (~ (r2_hidden @ X20 @ X19)
% 0.41/0.61          | ((X20) = (X17))
% 0.41/0.61          | ((X19) != (k1_tarski @ X17)))),
% 0.41/0.61      inference('cnf', [status(esa)], [d1_tarski])).
% 0.41/0.61  thf('41', plain,
% 0.41/0.61      (![X17 : $i, X20 : $i]:
% 0.41/0.61         (((X20) = (X17)) | ~ (r2_hidden @ X20 @ (k1_tarski @ X17)))),
% 0.41/0.61      inference('simplify', [status(thm)], ['40'])).
% 0.41/0.61  thf('42', plain, (((k1_funct_1 @ sk_D @ sk_C_2) = (sk_B))),
% 0.41/0.61      inference('sup-', [status(thm)], ['39', '41'])).
% 0.41/0.61  thf('43', plain, (((k1_funct_1 @ sk_D @ sk_C_2) != (sk_B))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('44', plain, ($false),
% 0.41/0.61      inference('simplify_reflect-', [status(thm)], ['42', '43'])).
% 0.41/0.61  
% 0.41/0.61  % SZS output end Refutation
% 0.41/0.61  
% 0.41/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
