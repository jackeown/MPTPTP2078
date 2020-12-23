%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qvTO5rCFdZ

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:17 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :   79 (  98 expanded)
%              Number of leaves         :   37 (  46 expanded)
%              Depth                    :   14
%              Number of atoms          :  520 ( 895 expanded)
%              Number of equality atoms :   38 (  54 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X60: $i,X61: $i,X62: $i] :
      ( ( v5_relat_1 @ X60 @ X62 )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X61 @ X62 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X74: $i,X75: $i,X76: $i] :
      ( ~ ( v1_funct_2 @ X76 @ X74 @ X75 )
      | ( X74
        = ( k1_relset_1 @ X74 @ X75 @ X76 ) )
      | ~ ( zip_tseitin_1 @ X76 @ X75 @ X74 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ( ( k1_relset_1 @ X64 @ X65 @ X63 )
        = ( k1_relat_1 @ X63 ) )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X64 @ X65 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('9',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
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

thf('12',plain,(
    ! [X77: $i,X78: $i,X79: $i] :
      ( ~ ( zip_tseitin_0 @ X77 @ X78 )
      | ( zip_tseitin_1 @ X79 @ X77 @ X78 )
      | ~ ( m1_subset_1 @ X79 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X78 @ X77 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('13',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ~ ( zip_tseitin_0 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X72: $i,X73: $i] :
      ( ( zip_tseitin_0 @ X72 @ X73 )
      | ( X72 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('17',plain,(
    ! [X49: $i,X50: $i] :
      ( ( X50 != X49 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X50 ) @ ( k1_tarski @ X49 ) )
       != ( k1_tarski @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('18',plain,(
    ! [X49: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X49 ) @ ( k1_tarski @ X49 ) )
     != ( k1_tarski @ X49 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( zip_tseitin_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( zip_tseitin_0 @ ( k1_tarski @ X0 ) @ X1 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    zip_tseitin_1 @ sk_D_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['13','20'])).

thf('22',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['10','21'])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('23',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( r2_hidden @ X55 @ ( k1_relat_1 @ X56 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X56 @ X55 ) @ ( k2_relat_1 @ X56 ) )
      | ~ ( v1_funct_1 @ X56 )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D_1 )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ ( k2_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('26',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ( v1_relat_1 @ X57 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X58 @ X59 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('27',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ ( k2_relat_1 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['24','27','28'])).

thf('30',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['3','29'])).

thf(t202_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k2_relat_1 @ B ) )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('31',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( r2_hidden @ X52 @ ( k2_relat_1 @ X53 ) )
      | ( r2_hidden @ X52 @ X54 )
      | ~ ( v5_relat_1 @ X53 @ X54 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t202_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D_1 )
      | ~ ( v5_relat_1 @ sk_D_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v5_relat_1 @ sk_D_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_C_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_C_1 ) @ ( k1_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['2','34'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('36',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X18 )
      | ( X19 = X16 )
      | ( X18
       != ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('37',plain,(
    ! [X16: $i,X19: $i] :
      ( ( X19 = X16 )
      | ~ ( r2_hidden @ X19 @ ( k1_tarski @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( k1_funct_1 @ sk_D_1 @ sk_C_1 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ( k1_funct_1 @ sk_D_1 @ sk_C_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['38','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qvTO5rCFdZ
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:11:20 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.61/0.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.61/0.78  % Solved by: fo/fo7.sh
% 0.61/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.78  % done 475 iterations in 0.334s
% 0.61/0.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.61/0.78  % SZS output start Refutation
% 0.61/0.78  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.61/0.78  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.61/0.78  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.61/0.78  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.61/0.78  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.61/0.78  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.61/0.78  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.61/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.78  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.61/0.78  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.61/0.78  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.61/0.78  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.61/0.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.61/0.78  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.61/0.78  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.61/0.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.61/0.78  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.61/0.78  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.61/0.78  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.61/0.78  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.61/0.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.61/0.78  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.61/0.78  thf(t65_funct_2, conjecture,
% 0.61/0.78    (![A:$i,B:$i,C:$i,D:$i]:
% 0.61/0.78     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.61/0.78         ( m1_subset_1 @
% 0.61/0.78           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.61/0.78       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.61/0.78  thf(zf_stmt_0, negated_conjecture,
% 0.61/0.78    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.61/0.78        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.61/0.78            ( m1_subset_1 @
% 0.61/0.78              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.61/0.78          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.61/0.78    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.61/0.78  thf('0', plain,
% 0.61/0.78      ((m1_subset_1 @ sk_D_1 @ 
% 0.61/0.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.61/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.78  thf(cc2_relset_1, axiom,
% 0.61/0.78    (![A:$i,B:$i,C:$i]:
% 0.61/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.78       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.61/0.78  thf('1', plain,
% 0.61/0.78      (![X60 : $i, X61 : $i, X62 : $i]:
% 0.61/0.78         ((v5_relat_1 @ X60 @ X62)
% 0.61/0.78          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X61 @ X62))))),
% 0.61/0.78      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.61/0.78  thf('2', plain, ((v5_relat_1 @ sk_D_1 @ (k1_tarski @ sk_B_1))),
% 0.61/0.78      inference('sup-', [status(thm)], ['0', '1'])).
% 0.61/0.78  thf('3', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.61/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.78  thf('4', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.61/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.78  thf(d1_funct_2, axiom,
% 0.61/0.78    (![A:$i,B:$i,C:$i]:
% 0.61/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.78       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.61/0.78           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.61/0.78             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.61/0.78         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.61/0.78           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.61/0.78             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.61/0.78  thf(zf_stmt_1, axiom,
% 0.61/0.78    (![C:$i,B:$i,A:$i]:
% 0.61/0.78     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.61/0.78       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.61/0.78  thf('5', plain,
% 0.61/0.78      (![X74 : $i, X75 : $i, X76 : $i]:
% 0.61/0.78         (~ (v1_funct_2 @ X76 @ X74 @ X75)
% 0.61/0.78          | ((X74) = (k1_relset_1 @ X74 @ X75 @ X76))
% 0.61/0.78          | ~ (zip_tseitin_1 @ X76 @ X75 @ X74))),
% 0.61/0.78      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.61/0.78  thf('6', plain,
% 0.61/0.78      ((~ (zip_tseitin_1 @ sk_D_1 @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.61/0.78        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D_1)))),
% 0.61/0.78      inference('sup-', [status(thm)], ['4', '5'])).
% 0.61/0.78  thf('7', plain,
% 0.61/0.78      ((m1_subset_1 @ sk_D_1 @ 
% 0.61/0.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.61/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.78  thf(redefinition_k1_relset_1, axiom,
% 0.61/0.78    (![A:$i,B:$i,C:$i]:
% 0.61/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.78       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.61/0.78  thf('8', plain,
% 0.61/0.78      (![X63 : $i, X64 : $i, X65 : $i]:
% 0.61/0.78         (((k1_relset_1 @ X64 @ X65 @ X63) = (k1_relat_1 @ X63))
% 0.61/0.78          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X64 @ X65))))),
% 0.61/0.78      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.61/0.78  thf('9', plain,
% 0.61/0.78      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D_1)
% 0.61/0.78         = (k1_relat_1 @ sk_D_1))),
% 0.61/0.78      inference('sup-', [status(thm)], ['7', '8'])).
% 0.61/0.78  thf('10', plain,
% 0.61/0.78      ((~ (zip_tseitin_1 @ sk_D_1 @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.61/0.78        | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.61/0.78      inference('demod', [status(thm)], ['6', '9'])).
% 0.61/0.78  thf('11', plain,
% 0.61/0.78      ((m1_subset_1 @ sk_D_1 @ 
% 0.61/0.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.61/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.78  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.61/0.78  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.61/0.78  thf(zf_stmt_4, axiom,
% 0.61/0.78    (![B:$i,A:$i]:
% 0.61/0.78     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.61/0.78       ( zip_tseitin_0 @ B @ A ) ))).
% 0.61/0.78  thf(zf_stmt_5, axiom,
% 0.61/0.78    (![A:$i,B:$i,C:$i]:
% 0.61/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.78       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.61/0.78         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.61/0.78           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.61/0.78             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.61/0.78  thf('12', plain,
% 0.61/0.78      (![X77 : $i, X78 : $i, X79 : $i]:
% 0.61/0.78         (~ (zip_tseitin_0 @ X77 @ X78)
% 0.61/0.78          | (zip_tseitin_1 @ X79 @ X77 @ X78)
% 0.61/0.78          | ~ (m1_subset_1 @ X79 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X78 @ X77))))),
% 0.61/0.78      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.61/0.78  thf('13', plain,
% 0.61/0.78      (((zip_tseitin_1 @ sk_D_1 @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.61/0.78        | ~ (zip_tseitin_0 @ (k1_tarski @ sk_B_1) @ sk_A))),
% 0.61/0.78      inference('sup-', [status(thm)], ['11', '12'])).
% 0.61/0.78  thf('14', plain,
% 0.61/0.78      (![X72 : $i, X73 : $i]:
% 0.61/0.78         ((zip_tseitin_0 @ X72 @ X73) | ((X72) = (k1_xboole_0)))),
% 0.61/0.78      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.61/0.78  thf(t3_boole, axiom,
% 0.61/0.78    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.61/0.78  thf('15', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.61/0.78      inference('cnf', [status(esa)], [t3_boole])).
% 0.61/0.78  thf('16', plain,
% 0.61/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.78         (((k4_xboole_0 @ X1 @ X0) = (X1)) | (zip_tseitin_0 @ X0 @ X2))),
% 0.61/0.78      inference('sup+', [status(thm)], ['14', '15'])).
% 0.61/0.78  thf(t20_zfmisc_1, axiom,
% 0.61/0.78    (![A:$i,B:$i]:
% 0.61/0.78     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.61/0.78         ( k1_tarski @ A ) ) <=>
% 0.61/0.78       ( ( A ) != ( B ) ) ))).
% 0.61/0.78  thf('17', plain,
% 0.61/0.78      (![X49 : $i, X50 : $i]:
% 0.61/0.78         (((X50) != (X49))
% 0.61/0.78          | ((k4_xboole_0 @ (k1_tarski @ X50) @ (k1_tarski @ X49))
% 0.61/0.78              != (k1_tarski @ X50)))),
% 0.61/0.78      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.61/0.78  thf('18', plain,
% 0.61/0.78      (![X49 : $i]:
% 0.61/0.78         ((k4_xboole_0 @ (k1_tarski @ X49) @ (k1_tarski @ X49))
% 0.61/0.78           != (k1_tarski @ X49))),
% 0.61/0.78      inference('simplify', [status(thm)], ['17'])).
% 0.61/0.78  thf('19', plain,
% 0.61/0.78      (![X0 : $i, X1 : $i]:
% 0.61/0.78         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.61/0.78          | (zip_tseitin_0 @ (k1_tarski @ X0) @ X1))),
% 0.61/0.78      inference('sup-', [status(thm)], ['16', '18'])).
% 0.61/0.78  thf('20', plain,
% 0.61/0.78      (![X0 : $i, X1 : $i]: (zip_tseitin_0 @ (k1_tarski @ X0) @ X1)),
% 0.61/0.78      inference('simplify', [status(thm)], ['19'])).
% 0.61/0.78  thf('21', plain, ((zip_tseitin_1 @ sk_D_1 @ (k1_tarski @ sk_B_1) @ sk_A)),
% 0.61/0.78      inference('demod', [status(thm)], ['13', '20'])).
% 0.61/0.78  thf('22', plain, (((sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.61/0.78      inference('demod', [status(thm)], ['10', '21'])).
% 0.61/0.78  thf(t12_funct_1, axiom,
% 0.61/0.78    (![A:$i,B:$i]:
% 0.61/0.78     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.61/0.78       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.61/0.78         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.61/0.78  thf('23', plain,
% 0.61/0.78      (![X55 : $i, X56 : $i]:
% 0.61/0.78         (~ (r2_hidden @ X55 @ (k1_relat_1 @ X56))
% 0.61/0.78          | (r2_hidden @ (k1_funct_1 @ X56 @ X55) @ (k2_relat_1 @ X56))
% 0.61/0.78          | ~ (v1_funct_1 @ X56)
% 0.61/0.78          | ~ (v1_relat_1 @ X56))),
% 0.61/0.78      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.61/0.78  thf('24', plain,
% 0.61/0.78      (![X0 : $i]:
% 0.61/0.78         (~ (r2_hidden @ X0 @ sk_A)
% 0.61/0.78          | ~ (v1_relat_1 @ sk_D_1)
% 0.61/0.78          | ~ (v1_funct_1 @ sk_D_1)
% 0.61/0.78          | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ (k2_relat_1 @ sk_D_1)))),
% 0.61/0.78      inference('sup-', [status(thm)], ['22', '23'])).
% 0.61/0.78  thf('25', plain,
% 0.61/0.78      ((m1_subset_1 @ sk_D_1 @ 
% 0.61/0.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.61/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.78  thf(cc1_relset_1, axiom,
% 0.61/0.78    (![A:$i,B:$i,C:$i]:
% 0.61/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.78       ( v1_relat_1 @ C ) ))).
% 0.61/0.78  thf('26', plain,
% 0.61/0.78      (![X57 : $i, X58 : $i, X59 : $i]:
% 0.61/0.78         ((v1_relat_1 @ X57)
% 0.61/0.78          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X59))))),
% 0.61/0.78      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.61/0.78  thf('27', plain, ((v1_relat_1 @ sk_D_1)),
% 0.61/0.78      inference('sup-', [status(thm)], ['25', '26'])).
% 0.61/0.78  thf('28', plain, ((v1_funct_1 @ sk_D_1)),
% 0.61/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.78  thf('29', plain,
% 0.61/0.78      (![X0 : $i]:
% 0.61/0.78         (~ (r2_hidden @ X0 @ sk_A)
% 0.61/0.78          | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ (k2_relat_1 @ sk_D_1)))),
% 0.61/0.78      inference('demod', [status(thm)], ['24', '27', '28'])).
% 0.61/0.78  thf('30', plain,
% 0.61/0.78      ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_C_1) @ (k2_relat_1 @ sk_D_1))),
% 0.61/0.78      inference('sup-', [status(thm)], ['3', '29'])).
% 0.61/0.78  thf(t202_relat_1, axiom,
% 0.61/0.78    (![A:$i,B:$i]:
% 0.61/0.78     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.61/0.78       ( ![C:$i]:
% 0.61/0.78         ( ( r2_hidden @ C @ ( k2_relat_1 @ B ) ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.61/0.78  thf('31', plain,
% 0.61/0.78      (![X52 : $i, X53 : $i, X54 : $i]:
% 0.61/0.78         (~ (r2_hidden @ X52 @ (k2_relat_1 @ X53))
% 0.61/0.78          | (r2_hidden @ X52 @ X54)
% 0.61/0.78          | ~ (v5_relat_1 @ X53 @ X54)
% 0.61/0.78          | ~ (v1_relat_1 @ X53))),
% 0.61/0.78      inference('cnf', [status(esa)], [t202_relat_1])).
% 0.61/0.78  thf('32', plain,
% 0.61/0.78      (![X0 : $i]:
% 0.61/0.78         (~ (v1_relat_1 @ sk_D_1)
% 0.61/0.78          | ~ (v5_relat_1 @ sk_D_1 @ X0)
% 0.61/0.78          | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_C_1) @ X0))),
% 0.61/0.78      inference('sup-', [status(thm)], ['30', '31'])).
% 0.61/0.78  thf('33', plain, ((v1_relat_1 @ sk_D_1)),
% 0.61/0.78      inference('sup-', [status(thm)], ['25', '26'])).
% 0.61/0.78  thf('34', plain,
% 0.61/0.78      (![X0 : $i]:
% 0.61/0.78         (~ (v5_relat_1 @ sk_D_1 @ X0)
% 0.61/0.78          | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_C_1) @ X0))),
% 0.61/0.78      inference('demod', [status(thm)], ['32', '33'])).
% 0.61/0.78  thf('35', plain,
% 0.61/0.78      ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_C_1) @ (k1_tarski @ sk_B_1))),
% 0.61/0.78      inference('sup-', [status(thm)], ['2', '34'])).
% 0.61/0.78  thf(d1_tarski, axiom,
% 0.61/0.78    (![A:$i,B:$i]:
% 0.61/0.78     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.61/0.78       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.61/0.78  thf('36', plain,
% 0.61/0.78      (![X16 : $i, X18 : $i, X19 : $i]:
% 0.61/0.78         (~ (r2_hidden @ X19 @ X18)
% 0.61/0.78          | ((X19) = (X16))
% 0.61/0.78          | ((X18) != (k1_tarski @ X16)))),
% 0.61/0.78      inference('cnf', [status(esa)], [d1_tarski])).
% 0.61/0.78  thf('37', plain,
% 0.61/0.78      (![X16 : $i, X19 : $i]:
% 0.61/0.78         (((X19) = (X16)) | ~ (r2_hidden @ X19 @ (k1_tarski @ X16)))),
% 0.61/0.78      inference('simplify', [status(thm)], ['36'])).
% 0.61/0.78  thf('38', plain, (((k1_funct_1 @ sk_D_1 @ sk_C_1) = (sk_B_1))),
% 0.61/0.78      inference('sup-', [status(thm)], ['35', '37'])).
% 0.61/0.78  thf('39', plain, (((k1_funct_1 @ sk_D_1 @ sk_C_1) != (sk_B_1))),
% 0.61/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.78  thf('40', plain, ($false),
% 0.61/0.78      inference('simplify_reflect-', [status(thm)], ['38', '39'])).
% 0.61/0.78  
% 0.61/0.78  % SZS output end Refutation
% 0.61/0.78  
% 0.61/0.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
