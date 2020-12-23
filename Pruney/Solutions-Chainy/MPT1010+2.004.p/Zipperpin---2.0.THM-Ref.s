%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MMJjGqQcJt

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:13 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 102 expanded)
%              Number of leaves         :   38 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :  510 ( 895 expanded)
%              Number of equality atoms :   30 (  48 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( v1_funct_2 @ X47 @ X45 @ X46 )
      | ( X45
        = ( k1_relset_1 @ X45 @ X46 @ X47 ) )
      | ~ ( zip_tseitin_2 @ X47 @ X46 @ X45 ) ) ),
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
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( zip_tseitin_1 @ X48 @ X49 )
      | ( zip_tseitin_2 @ X50 @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_1 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X43: $i,X44: $i] :
      ( ( zip_tseitin_1 @ X43 @ X44 )
      | ( X43 = k1_xboole_0 ) ) ),
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
    ! [X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X32 @ X33 )
      | ~ ( r1_tarski @ X33 @ X32 ) ) ),
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
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( ( k1_relset_1 @ X41 @ X42 @ X40 )
        = ( k1_relat_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ) ),
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
    ! [X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X30 @ ( k1_relat_1 @ X31 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X31 @ X30 ) @ ( k2_relat_1 @ X31 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
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

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('23',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v1_relat_1 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('24',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['21','24','25'])).

thf('27',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C_2 ) @ ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['0','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('29',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( v5_relat_1 @ X37 @ X39 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('30',plain,(
    v5_relat_1 @ sk_D @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('31',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v5_relat_1 @ X28 @ X29 )
      | ( r1_tarski @ ( k2_relat_1 @ X28 ) @ X29 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['22','23'])).

thf('34',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C_2 ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['27','36'])).

thf('38',plain,(
    ! [X17: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X20 @ X19 )
      | ( X20 = X17 )
      | ( X19
       != ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('39',plain,(
    ! [X17: $i,X20: $i] :
      ( ( X20 = X17 )
      | ~ ( r2_hidden @ X20 @ ( k1_tarski @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( k1_funct_1 @ sk_D @ sk_C_2 )
    = sk_B ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    ( k1_funct_1 @ sk_D @ sk_C_2 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MMJjGqQcJt
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:39:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.40/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.60  % Solved by: fo/fo7.sh
% 0.40/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.60  % done 183 iterations in 0.152s
% 0.40/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.60  % SZS output start Refutation
% 0.40/0.60  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.40/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.40/0.60  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.40/0.60  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.40/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.60  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.40/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.60  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.40/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.60  thf(sk_D_type, type, sk_D: $i).
% 0.40/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.60  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.40/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.40/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.60  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.40/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.40/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.40/0.60  thf(t65_funct_2, conjecture,
% 0.40/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.60     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.40/0.60         ( m1_subset_1 @
% 0.40/0.60           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.40/0.60       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.40/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.60    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.60        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.40/0.60            ( m1_subset_1 @
% 0.40/0.60              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.40/0.60          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.40/0.60    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.40/0.60  thf('0', plain, ((r2_hidden @ sk_C_2 @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('1', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf(d1_funct_2, axiom,
% 0.40/0.60    (![A:$i,B:$i,C:$i]:
% 0.40/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.60       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.40/0.60           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.40/0.60             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.40/0.60         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.40/0.60           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.40/0.60             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.40/0.60  thf(zf_stmt_1, axiom,
% 0.40/0.60    (![C:$i,B:$i,A:$i]:
% 0.40/0.60     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.40/0.60       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.40/0.60  thf('2', plain,
% 0.40/0.60      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.40/0.60         (~ (v1_funct_2 @ X47 @ X45 @ X46)
% 0.40/0.60          | ((X45) = (k1_relset_1 @ X45 @ X46 @ X47))
% 0.40/0.60          | ~ (zip_tseitin_2 @ X47 @ X46 @ X45))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.40/0.60  thf('3', plain,
% 0.40/0.60      ((~ (zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 0.40/0.60        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.60  thf('4', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_D @ 
% 0.40/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.40/0.60  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $o).
% 0.40/0.60  thf(zf_stmt_4, axiom,
% 0.40/0.60    (![B:$i,A:$i]:
% 0.40/0.60     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.40/0.60       ( zip_tseitin_1 @ B @ A ) ))).
% 0.40/0.60  thf(zf_stmt_5, axiom,
% 0.40/0.60    (![A:$i,B:$i,C:$i]:
% 0.40/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.60       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.40/0.60         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.40/0.60           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.40/0.60             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.40/0.60  thf('5', plain,
% 0.40/0.60      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.40/0.60         (~ (zip_tseitin_1 @ X48 @ X49)
% 0.40/0.60          | (zip_tseitin_2 @ X50 @ X48 @ X49)
% 0.40/0.60          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X48))))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.40/0.60  thf('6', plain,
% 0.40/0.60      (((zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 0.40/0.60        | ~ (zip_tseitin_1 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.40/0.60      inference('sup-', [status(thm)], ['4', '5'])).
% 0.40/0.60  thf('7', plain,
% 0.40/0.60      (![X43 : $i, X44 : $i]:
% 0.40/0.60         ((zip_tseitin_1 @ X43 @ X44) | ((X43) = (k1_xboole_0)))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.40/0.60  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.40/0.60  thf('8', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.40/0.60      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.40/0.60  thf('9', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.60         ((r1_tarski @ X0 @ X1) | (zip_tseitin_1 @ X0 @ X2))),
% 0.40/0.60      inference('sup+', [status(thm)], ['7', '8'])).
% 0.40/0.60  thf(d1_tarski, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.40/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.40/0.60  thf('10', plain,
% 0.40/0.60      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.40/0.60         (((X18) != (X17))
% 0.40/0.60          | (r2_hidden @ X18 @ X19)
% 0.40/0.60          | ((X19) != (k1_tarski @ X17)))),
% 0.40/0.60      inference('cnf', [status(esa)], [d1_tarski])).
% 0.40/0.60  thf('11', plain, (![X17 : $i]: (r2_hidden @ X17 @ (k1_tarski @ X17))),
% 0.40/0.60      inference('simplify', [status(thm)], ['10'])).
% 0.40/0.60  thf(t7_ordinal1, axiom,
% 0.40/0.60    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.40/0.60  thf('12', plain,
% 0.40/0.60      (![X32 : $i, X33 : $i]:
% 0.40/0.60         (~ (r2_hidden @ X32 @ X33) | ~ (r1_tarski @ X33 @ X32))),
% 0.40/0.60      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.40/0.60  thf('13', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_tarski @ X0) @ X0)),
% 0.40/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.40/0.60  thf('14', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]: (zip_tseitin_1 @ (k1_tarski @ X0) @ X1)),
% 0.40/0.60      inference('sup-', [status(thm)], ['9', '13'])).
% 0.40/0.60  thf('15', plain, ((zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)),
% 0.40/0.60      inference('demod', [status(thm)], ['6', '14'])).
% 0.40/0.60  thf('16', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_D @ 
% 0.40/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf(redefinition_k1_relset_1, axiom,
% 0.40/0.60    (![A:$i,B:$i,C:$i]:
% 0.40/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.60       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.40/0.60  thf('17', plain,
% 0.40/0.60      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.40/0.60         (((k1_relset_1 @ X41 @ X42 @ X40) = (k1_relat_1 @ X40))
% 0.40/0.60          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42))))),
% 0.40/0.60      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.40/0.60  thf('18', plain,
% 0.40/0.60      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.40/0.60      inference('sup-', [status(thm)], ['16', '17'])).
% 0.40/0.60  thf('19', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.40/0.60      inference('demod', [status(thm)], ['3', '15', '18'])).
% 0.40/0.60  thf(t12_funct_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.40/0.60       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.40/0.60         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.40/0.60  thf('20', plain,
% 0.40/0.60      (![X30 : $i, X31 : $i]:
% 0.40/0.60         (~ (r2_hidden @ X30 @ (k1_relat_1 @ X31))
% 0.40/0.60          | (r2_hidden @ (k1_funct_1 @ X31 @ X30) @ (k2_relat_1 @ X31))
% 0.40/0.60          | ~ (v1_funct_1 @ X31)
% 0.40/0.60          | ~ (v1_relat_1 @ X31))),
% 0.40/0.60      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.40/0.60  thf('21', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (~ (r2_hidden @ X0 @ sk_A)
% 0.40/0.60          | ~ (v1_relat_1 @ sk_D)
% 0.40/0.60          | ~ (v1_funct_1 @ sk_D)
% 0.40/0.60          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['19', '20'])).
% 0.40/0.60  thf('22', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_D @ 
% 0.40/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf(cc1_relset_1, axiom,
% 0.40/0.60    (![A:$i,B:$i,C:$i]:
% 0.40/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.60       ( v1_relat_1 @ C ) ))).
% 0.40/0.60  thf('23', plain,
% 0.40/0.60      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.40/0.60         ((v1_relat_1 @ X34)
% 0.40/0.60          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.40/0.60      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.40/0.60  thf('24', plain, ((v1_relat_1 @ sk_D)),
% 0.40/0.60      inference('sup-', [status(thm)], ['22', '23'])).
% 0.40/0.60  thf('25', plain, ((v1_funct_1 @ sk_D)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('26', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (~ (r2_hidden @ X0 @ sk_A)
% 0.40/0.60          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D)))),
% 0.40/0.60      inference('demod', [status(thm)], ['21', '24', '25'])).
% 0.40/0.60  thf('27', plain,
% 0.40/0.60      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_C_2) @ (k2_relat_1 @ sk_D))),
% 0.40/0.60      inference('sup-', [status(thm)], ['0', '26'])).
% 0.40/0.60  thf('28', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_D @ 
% 0.40/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf(cc2_relset_1, axiom,
% 0.40/0.60    (![A:$i,B:$i,C:$i]:
% 0.40/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.60       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.40/0.60  thf('29', plain,
% 0.40/0.60      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.40/0.60         ((v5_relat_1 @ X37 @ X39)
% 0.40/0.60          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 0.40/0.60      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.40/0.60  thf('30', plain, ((v5_relat_1 @ sk_D @ (k1_tarski @ sk_B))),
% 0.40/0.60      inference('sup-', [status(thm)], ['28', '29'])).
% 0.40/0.60  thf(d19_relat_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( v1_relat_1 @ B ) =>
% 0.40/0.60       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.40/0.60  thf('31', plain,
% 0.40/0.60      (![X28 : $i, X29 : $i]:
% 0.40/0.60         (~ (v5_relat_1 @ X28 @ X29)
% 0.40/0.60          | (r1_tarski @ (k2_relat_1 @ X28) @ X29)
% 0.40/0.60          | ~ (v1_relat_1 @ X28))),
% 0.40/0.60      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.40/0.60  thf('32', plain,
% 0.40/0.60      ((~ (v1_relat_1 @ sk_D)
% 0.40/0.60        | (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_tarski @ sk_B)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['30', '31'])).
% 0.40/0.60  thf('33', plain, ((v1_relat_1 @ sk_D)),
% 0.40/0.60      inference('sup-', [status(thm)], ['22', '23'])).
% 0.40/0.60  thf('34', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_tarski @ sk_B))),
% 0.40/0.60      inference('demod', [status(thm)], ['32', '33'])).
% 0.40/0.60  thf(d3_tarski, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( r1_tarski @ A @ B ) <=>
% 0.40/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.40/0.60  thf('35', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.60         (~ (r2_hidden @ X0 @ X1)
% 0.40/0.60          | (r2_hidden @ X0 @ X2)
% 0.40/0.60          | ~ (r1_tarski @ X1 @ X2))),
% 0.40/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.60  thf('36', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         ((r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.40/0.60          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['34', '35'])).
% 0.40/0.60  thf('37', plain,
% 0.40/0.60      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_C_2) @ (k1_tarski @ sk_B))),
% 0.40/0.60      inference('sup-', [status(thm)], ['27', '36'])).
% 0.40/0.60  thf('38', plain,
% 0.40/0.60      (![X17 : $i, X19 : $i, X20 : $i]:
% 0.40/0.60         (~ (r2_hidden @ X20 @ X19)
% 0.40/0.60          | ((X20) = (X17))
% 0.40/0.60          | ((X19) != (k1_tarski @ X17)))),
% 0.40/0.60      inference('cnf', [status(esa)], [d1_tarski])).
% 0.40/0.60  thf('39', plain,
% 0.40/0.60      (![X17 : $i, X20 : $i]:
% 0.40/0.60         (((X20) = (X17)) | ~ (r2_hidden @ X20 @ (k1_tarski @ X17)))),
% 0.40/0.60      inference('simplify', [status(thm)], ['38'])).
% 0.40/0.60  thf('40', plain, (((k1_funct_1 @ sk_D @ sk_C_2) = (sk_B))),
% 0.40/0.60      inference('sup-', [status(thm)], ['37', '39'])).
% 0.40/0.60  thf('41', plain, (((k1_funct_1 @ sk_D @ sk_C_2) != (sk_B))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('42', plain, ($false),
% 0.40/0.60      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 0.40/0.60  
% 0.40/0.60  % SZS output end Refutation
% 0.40/0.60  
% 0.40/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
