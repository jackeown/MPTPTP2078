%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2lXtUKe4JM

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 (  63 expanded)
%              Number of leaves         :   27 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :  365 ( 547 expanded)
%              Number of equality atoms :   34 (  43 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X4 )
      | ( X1 = X2 )
      | ( X1 = X3 )
      | ( X1 = X4 ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X26 @ X27 )
      | ( X28 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X29 @ X26 ) @ X28 ) ) ),
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

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('8',plain,(
    ! [X14: $i] :
      ( ( k2_tarski @ X14 @ X14 )
      = ( k1_tarski @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_tarski @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X12 ) @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('10',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X24 ) @ X25 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['7','12'])).

thf('14',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['1','13'])).

thf('15',plain,(
    ! [X14: $i] :
      ( ( k2_tarski @ X14 @ X14 )
      = ( k1_tarski @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_enumset1 @ X15 @ X15 @ X16 )
      = ( k2_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( zip_tseitin_0 @ X10 @ X6 @ X7 @ X8 )
      | ( X9
       != ( k1_enumset1 @ X8 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('18',plain,(
    ! [X6: $i,X7: $i,X8: $i,X10: $i] :
      ( ~ ( zip_tseitin_0 @ X10 @ X6 @ X7 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k1_enumset1 @ X8 @ X7 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','19'])).

thf('21',plain,(
    ~ ( zip_tseitin_0 @ ( k1_funct_1 @ sk_D @ sk_C ) @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,
    ( ( ( k1_funct_1 @ sk_D @ sk_C )
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
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2lXtUKe4JM
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:19:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 60 iterations in 0.029s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.47  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.47  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.47  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.47  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.47  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.47  thf(d1_enumset1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.47       ( ![E:$i]:
% 0.21/0.47         ( ( r2_hidden @ E @ D ) <=>
% 0.21/0.47           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, axiom,
% 0.21/0.47    (![E:$i,C:$i,B:$i,A:$i]:
% 0.21/0.47     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.21/0.47       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.47         ((zip_tseitin_0 @ X1 @ X2 @ X3 @ X4)
% 0.21/0.47          | ((X1) = (X2))
% 0.21/0.47          | ((X1) = (X3))
% 0.21/0.47          | ((X1) = (X4)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t65_funct_2, conjecture,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.21/0.47         ( m1_subset_1 @
% 0.21/0.47           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.21/0.47       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_1, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.21/0.47            ( m1_subset_1 @
% 0.21/0.47              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.21/0.47          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.21/0.47  thf('1', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_D @ 
% 0.21/0.47        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.47  thf(t7_funct_2, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.47         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.47       ( ( r2_hidden @ C @ A ) =>
% 0.21/0.47         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.47           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X26 @ X27)
% 0.21/0.47          | ((X28) = (k1_xboole_0))
% 0.21/0.47          | ~ (v1_funct_1 @ X29)
% 0.21/0.47          | ~ (v1_funct_2 @ X29 @ X27 @ X28)
% 0.21/0.47          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.21/0.47          | (r2_hidden @ (k1_funct_1 @ X29 @ X26) @ X28))),
% 0.21/0.47      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.21/0.47          | ~ (v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))
% 0.21/0.47          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.47          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.21/0.47          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.47  thf('5', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.47  thf('6', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.21/0.47          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.21/0.47          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.21/0.47  thf(t69_enumset1, axiom,
% 0.21/0.47    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.47  thf('8', plain, (![X14 : $i]: ((k2_tarski @ X14 @ X14) = (k1_tarski @ X14))),
% 0.21/0.47      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.47  thf(t41_enumset1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( k2_tarski @ A @ B ) =
% 0.21/0.47       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X12 : $i, X13 : $i]:
% 0.21/0.47         ((k2_tarski @ X12 @ X13)
% 0.21/0.47           = (k2_xboole_0 @ (k1_tarski @ X12) @ (k1_tarski @ X13)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.21/0.47  thf(t49_zfmisc_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (![X24 : $i, X25 : $i]:
% 0.21/0.47         ((k2_xboole_0 @ (k1_tarski @ X24) @ X25) != (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) != (k1_xboole_0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.47  thf('12', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['8', '11'])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.21/0.47          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['7', '12'])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_C) @ (k1_tarski @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '13'])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      (![X14 : $i]: ((k2_tarski @ X14 @ X14) = (k1_tarski @ X14))),
% 0.21/0.47      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.47  thf(t70_enumset1, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      (![X15 : $i, X16 : $i]:
% 0.21/0.47         ((k1_enumset1 @ X15 @ X15 @ X16) = (k2_tarski @ X15 @ X16))),
% 0.21/0.47      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.47  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.47  thf(zf_stmt_3, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.47       ( ![E:$i]:
% 0.21/0.47         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X10 @ X9)
% 0.21/0.47          | ~ (zip_tseitin_0 @ X10 @ X6 @ X7 @ X8)
% 0.21/0.47          | ((X9) != (k1_enumset1 @ X8 @ X7 @ X6)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      (![X6 : $i, X7 : $i, X8 : $i, X10 : $i]:
% 0.21/0.47         (~ (zip_tseitin_0 @ X10 @ X6 @ X7 @ X8)
% 0.21/0.47          | ~ (r2_hidden @ X10 @ (k1_enumset1 @ X8 @ X7 @ X6)))),
% 0.21/0.47      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.21/0.47          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['16', '18'])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.21/0.47          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['15', '19'])).
% 0.21/0.47  thf('21', plain,
% 0.21/0.47      (~ (zip_tseitin_0 @ (k1_funct_1 @ sk_D @ sk_C) @ sk_B @ sk_B @ sk_B)),
% 0.21/0.47      inference('sup-', [status(thm)], ['14', '20'])).
% 0.21/0.47  thf('22', plain,
% 0.21/0.47      ((((k1_funct_1 @ sk_D @ sk_C) = (sk_B))
% 0.21/0.47        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B))
% 0.21/0.47        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '21'])).
% 0.21/0.47  thf('23', plain, (((k1_funct_1 @ sk_D @ sk_C) = (sk_B))),
% 0.21/0.47      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.47  thf('24', plain, (((k1_funct_1 @ sk_D @ sk_C) != (sk_B))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.47  thf('25', plain, ($false),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
