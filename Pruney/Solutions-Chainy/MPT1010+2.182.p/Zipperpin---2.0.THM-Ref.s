%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ksC5BB6r4W

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:38 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   56 (  64 expanded)
%              Number of leaves         :   29 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :  404 ( 580 expanded)
%              Number of equality atoms :   38 (  46 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(d2_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( E
        = ( k2_enumset1 @ A @ B @ C @ D ) )
    <=> ! [F: $i] :
          ( ( r2_hidden @ F @ E )
        <=> ~ ( ( F != D )
              & ( F != C )
              & ( F != B )
              & ( F != A ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [F: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ D @ C @ B @ A )
    <=> ( ( F != A )
        & ( F != B )
        & ( F != C )
        & ( F != D ) ) ) )).

thf('0',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 @ X18 )
      | ( X14 = X15 )
      | ( X14 = X16 )
      | ( X14 = X17 )
      | ( X14 = X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( k1_funct_1 @ D @ C )
          = B ) ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
       => ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ D @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_funct_2])).

thf('1',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('3',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ( X29 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X30 @ X27 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('9',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X11 ) @ X12 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['7','10'])).

thf('12',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('13',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k1_enumset1 @ X2 @ X2 @ X3 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('15',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_enumset1 @ X4 @ X4 @ X5 @ X6 )
      = ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( E
        = ( k2_enumset1 @ A @ B @ C @ D ) )
    <=> ! [F: $i] :
          ( ( r2_hidden @ F @ E )
        <=> ~ ( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X25 @ X24 )
      | ~ ( zip_tseitin_0 @ X25 @ X20 @ X21 @ X22 @ X23 )
      | ( X24
       != ( k2_enumset1 @ X23 @ X22 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('17',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X25: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X20 @ X21 @ X22 @ X23 )
      | ~ ( r2_hidden @ X25 @ ( k2_enumset1 @ X23 @ X22 @ X21 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('21',plain,(
    ~ ( zip_tseitin_0 @ ( k1_funct_1 @ sk_D @ sk_C ) @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['12','20'])).

thf('22',plain,
    ( ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B ) ),
    inference('sup-',[status(thm)],['0','21'])).

thf('23',plain,
    ( ( k1_funct_1 @ sk_D @ sk_C )
    = sk_B ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ( k1_funct_1 @ sk_D @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('25',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ksC5BB6r4W
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:33:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 39 iterations in 0.021s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.47  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.47  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.47  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.20/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.47  thf(d2_enumset1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.47     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.20/0.47       ( ![F:$i]:
% 0.20/0.47         ( ( r2_hidden @ F @ E ) <=>
% 0.20/0.47           ( ~( ( ( F ) != ( D ) ) & ( ( F ) != ( C ) ) & ( ( F ) != ( B ) ) & 
% 0.20/0.47                ( ( F ) != ( A ) ) ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, axiom,
% 0.20/0.47    (![F:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.20/0.47     ( ( zip_tseitin_0 @ F @ D @ C @ B @ A ) <=>
% 0.20/0.47       ( ( ( F ) != ( A ) ) & ( ( F ) != ( B ) ) & ( ( F ) != ( C ) ) & 
% 0.20/0.47         ( ( F ) != ( D ) ) ) ))).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.47         ((zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 @ X18)
% 0.20/0.47          | ((X14) = (X15))
% 0.20/0.47          | ((X14) = (X16))
% 0.20/0.47          | ((X14) = (X17))
% 0.20/0.47          | ((X14) = (X18)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t65_funct_2, conjecture,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.47     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.20/0.47         ( m1_subset_1 @
% 0.20/0.47           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.20/0.47       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_1, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.47        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.20/0.47            ( m1_subset_1 @
% 0.20/0.47              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.20/0.47          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.20/0.47  thf('1', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_D @ 
% 0.20/0.47        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.47  thf(t7_funct_2, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.47     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.47         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.47       ( ( r2_hidden @ C @ A ) =>
% 0.20/0.47         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.47           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X27 @ X28)
% 0.20/0.47          | ((X29) = (k1_xboole_0))
% 0.20/0.47          | ~ (v1_funct_1 @ X30)
% 0.20/0.47          | ~ (v1_funct_2 @ X30 @ X28 @ X29)
% 0.20/0.47          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.20/0.47          | (r2_hidden @ (k1_funct_1 @ X30 @ X27) @ X29))),
% 0.20/0.47      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.20/0.47          | ~ (v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))
% 0.20/0.47          | ~ (v1_funct_1 @ sk_D)
% 0.20/0.47          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.20/0.47          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.47  thf('5', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.47  thf('6', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.20/0.47          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.20/0.47          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.20/0.47  thf(t1_boole, axiom,
% 0.20/0.47    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.47  thf('8', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.47      inference('cnf', [status(esa)], [t1_boole])).
% 0.20/0.47  thf(t49_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X11 : $i, X12 : $i]:
% 0.20/0.47         ((k2_xboole_0 @ (k1_tarski @ X11) @ X12) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.20/0.47  thf('10', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.20/0.47          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['7', '10'])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_C) @ (k1_tarski @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '11'])).
% 0.20/0.47  thf(t69_enumset1, axiom,
% 0.20/0.47    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.47  thf('13', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.20/0.47      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.47  thf(t70_enumset1, axiom,
% 0.20/0.47    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X2 : $i, X3 : $i]:
% 0.20/0.47         ((k1_enumset1 @ X2 @ X2 @ X3) = (k2_tarski @ X2 @ X3))),
% 0.20/0.47      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.47  thf(t71_enumset1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.47         ((k2_enumset1 @ X4 @ X4 @ X5 @ X6) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 0.20/0.47      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.20/0.47  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.20/0.47  thf(zf_stmt_3, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.47     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.20/0.47       ( ![F:$i]:
% 0.20/0.47         ( ( r2_hidden @ F @ E ) <=> ( ~( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) ) ))).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X25 @ X24)
% 0.20/0.47          | ~ (zip_tseitin_0 @ X25 @ X20 @ X21 @ X22 @ X23)
% 0.20/0.47          | ((X24) != (k2_enumset1 @ X23 @ X22 @ X21 @ X20)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X25 : $i]:
% 0.20/0.47         (~ (zip_tseitin_0 @ X25 @ X20 @ X21 @ X22 @ X23)
% 0.20/0.47          | ~ (r2_hidden @ X25 @ (k2_enumset1 @ X23 @ X22 @ X21 @ X20)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.20/0.47          | ~ (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2))),
% 0.20/0.47      inference('sup-', [status(thm)], ['15', '17'])).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.20/0.47          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['14', '18'])).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.20/0.47          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['13', '19'])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      (~ (zip_tseitin_0 @ (k1_funct_1 @ sk_D @ sk_C) @ sk_B @ sk_B @ sk_B @ 
% 0.20/0.47          sk_B)),
% 0.20/0.47      inference('sup-', [status(thm)], ['12', '20'])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      ((((k1_funct_1 @ sk_D @ sk_C) = (sk_B))
% 0.20/0.47        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B))
% 0.20/0.47        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B))
% 0.20/0.47        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['0', '21'])).
% 0.20/0.47  thf('23', plain, (((k1_funct_1 @ sk_D @ sk_C) = (sk_B))),
% 0.20/0.47      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.47  thf('24', plain, (((k1_funct_1 @ sk_D @ sk_C) != (sk_B))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.47  thf('25', plain, ($false),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
