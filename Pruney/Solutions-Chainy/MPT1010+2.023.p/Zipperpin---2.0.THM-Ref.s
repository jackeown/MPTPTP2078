%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wTovWGsoGp

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:16 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 106 expanded)
%              Number of leaves         :   39 (  50 expanded)
%              Depth                    :   15
%              Number of atoms          :  522 ( 879 expanded)
%              Number of equality atoms :   30 (  50 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( v5_relat_1 @ X37 @ X39 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_D @ ( k1_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( v1_funct_2 @ X47 @ X45 @ X46 )
      | ( X45
        = ( k1_relset_1 @ X45 @ X46 @ X47 ) )
      | ~ ( zip_tseitin_2 @ X47 @ X46 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,
    ( ~ ( zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf('7',plain,(
    ! [X43: $i,X44: $i] :
      ( ( zip_tseitin_1 @ X43 @ X44 )
      | ( X43 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('8',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('9',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('10',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X32 @ X33 )
      | ~ ( r1_tarski @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_1 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_1 @ B @ A )
         => ( zip_tseitin_2 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( zip_tseitin_1 @ X48 @ X49 )
      | ( zip_tseitin_2 @ X50 @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('16',plain,
    ( ( zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ~ ( zip_tseitin_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('18',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( X17 != X16 )
      | ( r2_hidden @ X17 @ X18 )
      | ( X18
       != ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('19',plain,(
    ! [X16: $i] :
      ( r2_hidden @ X16 @ ( k1_tarski @ X16 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['17','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('24',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( ( k1_relset_1 @ X41 @ X42 @ X40 )
        = ( k1_relat_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('25',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['6','22','25'])).

thf(t176_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v5_relat_1 @ C @ A )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ B @ ( k1_relat_1 @ C ) )
       => ( m1_subset_1 @ ( k1_funct_1 @ C @ B ) @ A ) ) ) )).

thf('27',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X29 @ ( k1_relat_1 @ X30 ) )
      | ( m1_subset_1 @ ( k1_funct_1 @ X30 @ X29 ) @ X31 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v5_relat_1 @ X30 @ X31 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t176_funct_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( m1_subset_1 @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('30',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v1_relat_1 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('31',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ( m1_subset_1 @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['28','31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ X0 )
      | ~ ( v5_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','33'])).

thf('35',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ ( k1_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['2','34'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('36',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r2_hidden @ X27 @ X28 )
      | ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('39',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ ( k1_tarski @ sk_B_1 ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X18 )
      | ( X19 = X16 )
      | ( X18
       != ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('41',plain,(
    ! [X16: $i,X19: $i] :
      ( ( X19 = X16 )
      | ~ ( r2_hidden @ X19 @ ( k1_tarski @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( k1_funct_1 @ sk_D @ sk_C_1 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    ( k1_funct_1 @ sk_D @ sk_C_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['42','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wTovWGsoGp
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:39:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.55  % Solved by: fo/fo7.sh
% 0.36/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.55  % done 98 iterations in 0.094s
% 0.36/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.55  % SZS output start Refutation
% 0.36/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.36/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.36/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.55  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.36/0.55  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.36/0.55  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.36/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.36/0.55  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.36/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.36/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.55  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.36/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.55  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.36/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.55  thf(t65_funct_2, conjecture,
% 0.36/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.55     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.36/0.55         ( m1_subset_1 @
% 0.36/0.55           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.36/0.55       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.36/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.55    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.55        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.36/0.55            ( m1_subset_1 @
% 0.36/0.55              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.36/0.55          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.36/0.55    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.36/0.55  thf('0', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_D @ 
% 0.36/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(cc2_relset_1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.55       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.36/0.55  thf('1', plain,
% 0.36/0.55      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.36/0.55         ((v5_relat_1 @ X37 @ X39)
% 0.36/0.55          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 0.36/0.55      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.36/0.55  thf('2', plain, ((v5_relat_1 @ sk_D @ (k1_tarski @ sk_B_1))),
% 0.36/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.36/0.55  thf('3', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('4', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(d1_funct_2, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.55       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.36/0.55           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.36/0.55             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.36/0.55         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.36/0.55           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.36/0.55             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.36/0.55  thf(zf_stmt_1, axiom,
% 0.36/0.55    (![C:$i,B:$i,A:$i]:
% 0.36/0.55     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.36/0.55       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.36/0.55  thf('5', plain,
% 0.36/0.55      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.36/0.55         (~ (v1_funct_2 @ X47 @ X45 @ X46)
% 0.36/0.55          | ((X45) = (k1_relset_1 @ X45 @ X46 @ X47))
% 0.36/0.55          | ~ (zip_tseitin_2 @ X47 @ X46 @ X45))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.36/0.55  thf('6', plain,
% 0.36/0.55      ((~ (zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.36/0.55        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.36/0.55  thf(zf_stmt_2, axiom,
% 0.36/0.55    (![B:$i,A:$i]:
% 0.36/0.55     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.36/0.55       ( zip_tseitin_1 @ B @ A ) ))).
% 0.36/0.55  thf('7', plain,
% 0.36/0.55      (![X43 : $i, X44 : $i]:
% 0.36/0.55         ((zip_tseitin_1 @ X43 @ X44) | ((X43) = (k1_xboole_0)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.36/0.55  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.36/0.55  thf('8', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.36/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.55  thf(d1_xboole_0, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.36/0.55  thf('9', plain,
% 0.36/0.55      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.36/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.36/0.55  thf(t7_ordinal1, axiom,
% 0.36/0.55    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.55  thf('10', plain,
% 0.36/0.55      (![X32 : $i, X33 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X32 @ X33) | ~ (r1_tarski @ X33 @ X32))),
% 0.36/0.55      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.36/0.55  thf('11', plain,
% 0.36/0.55      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.36/0.55  thf('12', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.55      inference('sup-', [status(thm)], ['8', '11'])).
% 0.36/0.55  thf('13', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_1 @ X0 @ X1))),
% 0.36/0.55      inference('sup+', [status(thm)], ['7', '12'])).
% 0.36/0.55  thf('14', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_D @ 
% 0.36/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.36/0.55  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $o).
% 0.36/0.55  thf(zf_stmt_5, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.55       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.36/0.55         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.36/0.55           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.36/0.55             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.36/0.55  thf('15', plain,
% 0.36/0.55      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.36/0.55         (~ (zip_tseitin_1 @ X48 @ X49)
% 0.36/0.55          | (zip_tseitin_2 @ X50 @ X48 @ X49)
% 0.36/0.55          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X48))))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.36/0.55  thf('16', plain,
% 0.36/0.55      (((zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.36/0.55        | ~ (zip_tseitin_1 @ (k1_tarski @ sk_B_1) @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['14', '15'])).
% 0.36/0.55  thf('17', plain,
% 0.36/0.55      (((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.36/0.55        | (zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B_1) @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['13', '16'])).
% 0.36/0.55  thf(d1_tarski, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.36/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.36/0.55  thf('18', plain,
% 0.36/0.55      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.36/0.55         (((X17) != (X16))
% 0.36/0.55          | (r2_hidden @ X17 @ X18)
% 0.36/0.55          | ((X18) != (k1_tarski @ X16)))),
% 0.36/0.55      inference('cnf', [status(esa)], [d1_tarski])).
% 0.36/0.55  thf('19', plain, (![X16 : $i]: (r2_hidden @ X16 @ (k1_tarski @ X16))),
% 0.36/0.55      inference('simplify', [status(thm)], ['18'])).
% 0.36/0.55  thf('20', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.36/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.36/0.55  thf('21', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['19', '20'])).
% 0.36/0.55  thf('22', plain, ((zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B_1) @ sk_A)),
% 0.36/0.55      inference('clc', [status(thm)], ['17', '21'])).
% 0.36/0.55  thf('23', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_D @ 
% 0.36/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(redefinition_k1_relset_1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.55       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.36/0.55  thf('24', plain,
% 0.36/0.55      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.36/0.55         (((k1_relset_1 @ X41 @ X42 @ X40) = (k1_relat_1 @ X40))
% 0.36/0.55          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42))))),
% 0.36/0.55      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.36/0.55  thf('25', plain,
% 0.36/0.55      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D)
% 0.36/0.55         = (k1_relat_1 @ sk_D))),
% 0.36/0.55      inference('sup-', [status(thm)], ['23', '24'])).
% 0.36/0.55  thf('26', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.36/0.55      inference('demod', [status(thm)], ['6', '22', '25'])).
% 0.36/0.55  thf(t176_funct_1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) & ( v1_funct_1 @ C ) ) =>
% 0.36/0.55       ( ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) =>
% 0.36/0.55         ( m1_subset_1 @ ( k1_funct_1 @ C @ B ) @ A ) ) ))).
% 0.36/0.55  thf('27', plain,
% 0.36/0.55      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X29 @ (k1_relat_1 @ X30))
% 0.36/0.55          | (m1_subset_1 @ (k1_funct_1 @ X30 @ X29) @ X31)
% 0.36/0.55          | ~ (v1_funct_1 @ X30)
% 0.36/0.55          | ~ (v5_relat_1 @ X30 @ X31)
% 0.36/0.55          | ~ (v1_relat_1 @ X30))),
% 0.36/0.55      inference('cnf', [status(esa)], [t176_funct_1])).
% 0.36/0.55  thf('28', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X0 @ sk_A)
% 0.36/0.55          | ~ (v1_relat_1 @ sk_D)
% 0.36/0.55          | ~ (v5_relat_1 @ sk_D @ X1)
% 0.36/0.55          | ~ (v1_funct_1 @ sk_D)
% 0.36/0.55          | (m1_subset_1 @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 0.36/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.36/0.55  thf('29', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_D @ 
% 0.36/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(cc1_relset_1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.55       ( v1_relat_1 @ C ) ))).
% 0.36/0.55  thf('30', plain,
% 0.36/0.55      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.36/0.55         ((v1_relat_1 @ X34)
% 0.36/0.55          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.36/0.55      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.36/0.55  thf('31', plain, ((v1_relat_1 @ sk_D)),
% 0.36/0.55      inference('sup-', [status(thm)], ['29', '30'])).
% 0.36/0.55  thf('32', plain, ((v1_funct_1 @ sk_D)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('33', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X0 @ sk_A)
% 0.36/0.55          | ~ (v5_relat_1 @ sk_D @ X1)
% 0.36/0.55          | (m1_subset_1 @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 0.36/0.55      inference('demod', [status(thm)], ['28', '31', '32'])).
% 0.36/0.55  thf('34', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((m1_subset_1 @ (k1_funct_1 @ sk_D @ sk_C_1) @ X0)
% 0.36/0.55          | ~ (v5_relat_1 @ sk_D @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['3', '33'])).
% 0.36/0.55  thf('35', plain,
% 0.36/0.55      ((m1_subset_1 @ (k1_funct_1 @ sk_D @ sk_C_1) @ (k1_tarski @ sk_B_1))),
% 0.36/0.55      inference('sup-', [status(thm)], ['2', '34'])).
% 0.36/0.55  thf(t2_subset, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ A @ B ) =>
% 0.36/0.55       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.36/0.55  thf('36', plain,
% 0.36/0.55      (![X27 : $i, X28 : $i]:
% 0.36/0.55         ((r2_hidden @ X27 @ X28)
% 0.36/0.55          | (v1_xboole_0 @ X28)
% 0.36/0.55          | ~ (m1_subset_1 @ X27 @ X28))),
% 0.36/0.55      inference('cnf', [status(esa)], [t2_subset])).
% 0.36/0.55  thf('37', plain,
% 0.36/0.55      (((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.36/0.55        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C_1) @ (k1_tarski @ sk_B_1)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['35', '36'])).
% 0.36/0.55  thf('38', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['19', '20'])).
% 0.36/0.55  thf('39', plain,
% 0.36/0.55      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_C_1) @ (k1_tarski @ sk_B_1))),
% 0.36/0.55      inference('clc', [status(thm)], ['37', '38'])).
% 0.36/0.55  thf('40', plain,
% 0.36/0.55      (![X16 : $i, X18 : $i, X19 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X19 @ X18)
% 0.36/0.55          | ((X19) = (X16))
% 0.36/0.55          | ((X18) != (k1_tarski @ X16)))),
% 0.36/0.55      inference('cnf', [status(esa)], [d1_tarski])).
% 0.36/0.55  thf('41', plain,
% 0.36/0.55      (![X16 : $i, X19 : $i]:
% 0.36/0.55         (((X19) = (X16)) | ~ (r2_hidden @ X19 @ (k1_tarski @ X16)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['40'])).
% 0.36/0.55  thf('42', plain, (((k1_funct_1 @ sk_D @ sk_C_1) = (sk_B_1))),
% 0.36/0.55      inference('sup-', [status(thm)], ['39', '41'])).
% 0.36/0.55  thf('43', plain, (((k1_funct_1 @ sk_D @ sk_C_1) != (sk_B_1))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('44', plain, ($false),
% 0.36/0.55      inference('simplify_reflect-', [status(thm)], ['42', '43'])).
% 0.36/0.55  
% 0.36/0.55  % SZS output end Refutation
% 0.36/0.55  
% 0.39/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
