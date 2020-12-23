%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ov0kjyYrIf

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   79 (  99 expanded)
%              Number of leaves         :   37 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :  496 ( 881 expanded)
%              Number of equality atoms :   30 (  48 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( v5_relat_1 @ X48 @ X50 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_D @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
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
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('5',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ~ ( v1_funct_2 @ X58 @ X56 @ X57 )
      | ( X56
        = ( k1_relset_1 @ X56 @ X57 @ X58 ) )
      | ~ ( zip_tseitin_1 @ X58 @ X57 @ X56 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
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

thf('8',plain,(
    ! [X59: $i,X60: $i,X61: $i] :
      ( ~ ( zip_tseitin_0 @ X59 @ X60 )
      | ( zip_tseitin_1 @ X61 @ X59 @ X60 )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X60 @ X59 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('9',plain,
    ( ( zip_tseitin_1 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X54: $i,X55: $i] :
      ( ( zip_tseitin_0 @ X54 @ X55 )
      | ( X54 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('13',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( X3 != X2 )
      | ( r2_hidden @ X3 @ X4 )
      | ( X4
       != ( k1_tarski @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('14',plain,(
    ! [X2: $i] :
      ( r2_hidden @ X2 @ ( k1_tarski @ X2 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('15',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( r2_hidden @ X43 @ X44 )
      | ~ ( r1_tarski @ X44 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('16',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( zip_tseitin_0 @ ( k1_tarski @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    zip_tseitin_1 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['9','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('20',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( ( k1_relset_1 @ X52 @ X53 @ X51 )
        = ( k1_relat_1 @ X51 ) )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X53 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('21',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['6','18','21'])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('23',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( r2_hidden @ X41 @ ( k1_relat_1 @ X42 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X42 @ X41 ) @ ( k2_relat_1 @ X42 ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('26',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( v1_relat_1 @ X45 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('27',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['24','27','28'])).

thf('30',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['3','29'])).

thf(t202_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k2_relat_1 @ B ) )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('31',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ X38 @ ( k2_relat_1 @ X39 ) )
      | ( r2_hidden @ X38 @ X40 )
      | ~ ( v5_relat_1 @ X39 @ X40 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t202_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ~ ( v5_relat_1 @ sk_D @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['25','26'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v5_relat_1 @ sk_D @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['2','34'])).

thf('36',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X5 @ X4 )
      | ( X5 = X2 )
      | ( X4
       != ( k1_tarski @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('37',plain,(
    ! [X2: $i,X5: $i] :
      ( ( X5 = X2 )
      | ~ ( r2_hidden @ X5 @ ( k1_tarski @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( k1_funct_1 @ sk_D @ sk_C_1 )
    = sk_B ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ( k1_funct_1 @ sk_D @ sk_C_1 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['38','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ov0kjyYrIf
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:15:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 88 iterations in 0.046s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.51  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.51  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.51  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.22/0.51  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.22/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.22/0.51  thf(t65_funct_2, conjecture,
% 0.22/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.51     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.22/0.51         ( m1_subset_1 @
% 0.22/0.51           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.22/0.51       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.51        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.22/0.51            ( m1_subset_1 @
% 0.22/0.51              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.22/0.51          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.22/0.51  thf('0', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_D @ 
% 0.22/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(cc2_relset_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.51       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.22/0.51  thf('1', plain,
% 0.22/0.51      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.22/0.51         ((v5_relat_1 @ X48 @ X50)
% 0.22/0.51          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50))))),
% 0.22/0.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.51  thf('2', plain, ((v5_relat_1 @ sk_D @ (k1_tarski @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.51  thf('3', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('4', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(d1_funct_2, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.51       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.22/0.51           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.22/0.51             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.22/0.51         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.22/0.51           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.22/0.51             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_1, axiom,
% 0.22/0.51    (![C:$i,B:$i,A:$i]:
% 0.22/0.51     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.22/0.51       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.22/0.51  thf('5', plain,
% 0.22/0.51      (![X56 : $i, X57 : $i, X58 : $i]:
% 0.22/0.51         (~ (v1_funct_2 @ X58 @ X56 @ X57)
% 0.22/0.51          | ((X56) = (k1_relset_1 @ X56 @ X57 @ X58))
% 0.22/0.51          | ~ (zip_tseitin_1 @ X58 @ X57 @ X56))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.51  thf('6', plain,
% 0.22/0.51      ((~ (zip_tseitin_1 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 0.22/0.51        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.51  thf('7', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_D @ 
% 0.22/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.22/0.51  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.22/0.51  thf(zf_stmt_4, axiom,
% 0.22/0.51    (![B:$i,A:$i]:
% 0.22/0.51     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.22/0.51       ( zip_tseitin_0 @ B @ A ) ))).
% 0.22/0.51  thf(zf_stmt_5, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.51       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.22/0.51         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.22/0.51           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.22/0.51             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.22/0.51  thf('8', plain,
% 0.22/0.51      (![X59 : $i, X60 : $i, X61 : $i]:
% 0.22/0.51         (~ (zip_tseitin_0 @ X59 @ X60)
% 0.22/0.51          | (zip_tseitin_1 @ X61 @ X59 @ X60)
% 0.22/0.51          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X59))))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.51  thf('9', plain,
% 0.22/0.51      (((zip_tseitin_1 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 0.22/0.51        | ~ (zip_tseitin_0 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.51  thf('10', plain,
% 0.22/0.51      (![X54 : $i, X55 : $i]:
% 0.22/0.51         ((zip_tseitin_0 @ X54 @ X55) | ((X54) = (k1_xboole_0)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.22/0.51  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.51  thf('11', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.51  thf('12', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 0.22/0.51      inference('sup+', [status(thm)], ['10', '11'])).
% 0.22/0.51  thf(d1_tarski, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.22/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.22/0.51  thf('13', plain,
% 0.22/0.51      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.51         (((X3) != (X2)) | (r2_hidden @ X3 @ X4) | ((X4) != (k1_tarski @ X2)))),
% 0.22/0.51      inference('cnf', [status(esa)], [d1_tarski])).
% 0.22/0.51  thf('14', plain, (![X2 : $i]: (r2_hidden @ X2 @ (k1_tarski @ X2))),
% 0.22/0.51      inference('simplify', [status(thm)], ['13'])).
% 0.22/0.51  thf(t7_ordinal1, axiom,
% 0.22/0.51    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.51  thf('15', plain,
% 0.22/0.51      (![X43 : $i, X44 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X43 @ X44) | ~ (r1_tarski @ X44 @ X43))),
% 0.22/0.51      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.22/0.51  thf('16', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_tarski @ X0) @ X0)),
% 0.22/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.51  thf('17', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]: (zip_tseitin_0 @ (k1_tarski @ X0) @ X1)),
% 0.22/0.51      inference('sup-', [status(thm)], ['12', '16'])).
% 0.22/0.51  thf('18', plain, ((zip_tseitin_1 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)),
% 0.22/0.51      inference('demod', [status(thm)], ['9', '17'])).
% 0.22/0.51  thf('19', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_D @ 
% 0.22/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(redefinition_k1_relset_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.51       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.22/0.51  thf('20', plain,
% 0.22/0.51      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.22/0.51         (((k1_relset_1 @ X52 @ X53 @ X51) = (k1_relat_1 @ X51))
% 0.22/0.51          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X53))))),
% 0.22/0.51      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.22/0.51  thf('21', plain,
% 0.22/0.51      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.22/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.51  thf('22', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.22/0.51      inference('demod', [status(thm)], ['6', '18', '21'])).
% 0.22/0.51  thf(t12_funct_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.51       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.22/0.51         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.22/0.51  thf('23', plain,
% 0.22/0.51      (![X41 : $i, X42 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X41 @ (k1_relat_1 @ X42))
% 0.22/0.51          | (r2_hidden @ (k1_funct_1 @ X42 @ X41) @ (k2_relat_1 @ X42))
% 0.22/0.51          | ~ (v1_funct_1 @ X42)
% 0.22/0.51          | ~ (v1_relat_1 @ X42))),
% 0.22/0.51      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.22/0.51  thf('24', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X0 @ sk_A)
% 0.22/0.51          | ~ (v1_relat_1 @ sk_D)
% 0.22/0.51          | ~ (v1_funct_1 @ sk_D)
% 0.22/0.51          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.51  thf('25', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_D @ 
% 0.22/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(cc1_relset_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.51       ( v1_relat_1 @ C ) ))).
% 0.22/0.51  thf('26', plain,
% 0.22/0.51      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.22/0.51         ((v1_relat_1 @ X45)
% 0.22/0.51          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47))))),
% 0.22/0.51      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.22/0.51  thf('27', plain, ((v1_relat_1 @ sk_D)),
% 0.22/0.51      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.51  thf('28', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('29', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X0 @ sk_A)
% 0.22/0.51          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D)))),
% 0.22/0.51      inference('demod', [status(thm)], ['24', '27', '28'])).
% 0.22/0.51  thf('30', plain,
% 0.22/0.51      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_C_1) @ (k2_relat_1 @ sk_D))),
% 0.22/0.51      inference('sup-', [status(thm)], ['3', '29'])).
% 0.22/0.51  thf(t202_relat_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.22/0.51       ( ![C:$i]:
% 0.22/0.51         ( ( r2_hidden @ C @ ( k2_relat_1 @ B ) ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.22/0.51  thf('31', plain,
% 0.22/0.51      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X38 @ (k2_relat_1 @ X39))
% 0.22/0.51          | (r2_hidden @ X38 @ X40)
% 0.22/0.51          | ~ (v5_relat_1 @ X39 @ X40)
% 0.22/0.51          | ~ (v1_relat_1 @ X39))),
% 0.22/0.51      inference('cnf', [status(esa)], [t202_relat_1])).
% 0.22/0.51  thf('32', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (v1_relat_1 @ sk_D)
% 0.22/0.51          | ~ (v5_relat_1 @ sk_D @ X0)
% 0.22/0.51          | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C_1) @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['30', '31'])).
% 0.22/0.51  thf('33', plain, ((v1_relat_1 @ sk_D)),
% 0.22/0.51      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.51  thf('34', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (v5_relat_1 @ sk_D @ X0)
% 0.22/0.51          | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C_1) @ X0))),
% 0.22/0.51      inference('demod', [status(thm)], ['32', '33'])).
% 0.22/0.51  thf('35', plain,
% 0.22/0.51      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_C_1) @ (k1_tarski @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['2', '34'])).
% 0.22/0.51  thf('36', plain,
% 0.22/0.51      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X5 @ X4) | ((X5) = (X2)) | ((X4) != (k1_tarski @ X2)))),
% 0.22/0.51      inference('cnf', [status(esa)], [d1_tarski])).
% 0.22/0.51  thf('37', plain,
% 0.22/0.51      (![X2 : $i, X5 : $i]:
% 0.22/0.51         (((X5) = (X2)) | ~ (r2_hidden @ X5 @ (k1_tarski @ X2)))),
% 0.22/0.51      inference('simplify', [status(thm)], ['36'])).
% 0.22/0.51  thf('38', plain, (((k1_funct_1 @ sk_D @ sk_C_1) = (sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['35', '37'])).
% 0.22/0.51  thf('39', plain, (((k1_funct_1 @ sk_D @ sk_C_1) != (sk_B))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('40', plain, ($false),
% 0.22/0.51      inference('simplify_reflect-', [status(thm)], ['38', '39'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
