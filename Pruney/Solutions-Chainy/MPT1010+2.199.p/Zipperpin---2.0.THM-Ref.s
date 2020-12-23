%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.B1lyM1vBln

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:40 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   60 (  68 expanded)
%              Number of leaves         :   31 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :  469 ( 645 expanded)
%              Number of equality atoms :   44 (  52 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(d3_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( F
        = ( k3_enumset1 @ A @ B @ C @ D @ E ) )
    <=> ! [G: $i] :
          ( ( r2_hidden @ G @ F )
        <=> ~ ( ( G != E )
              & ( G != D )
              & ( G != C )
              & ( G != B )
              & ( G != A ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [G: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A )
    <=> ( ( G != A )
        & ( G != B )
        & ( G != C )
        & ( G != D )
        & ( G != E ) ) ) )).

thf('0',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 )
      | ( X14 = X15 )
      | ( X14 = X16 )
      | ( X14 = X17 )
      | ( X14 = X18 )
      | ( X14 = X19 ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ X29 @ X30 )
      | ( X31 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X32 @ X29 ) @ X31 ) ) ),
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

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

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

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('16',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k3_enumset1 @ X7 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_enumset1 @ X7 @ X8 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( F
        = ( k3_enumset1 @ A @ B @ C @ D @ E ) )
    <=> ! [G: $i] :
          ( ( r2_hidden @ G @ F )
        <=> ~ ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X27 @ X26 )
      | ~ ( zip_tseitin_0 @ X27 @ X21 @ X22 @ X23 @ X24 @ X25 )
      | ( X26
       != ( k3_enumset1 @ X25 @ X24 @ X23 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('18',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X21 @ X22 @ X23 @ X24 @ X25 )
      | ~ ( r2_hidden @ X27 @ ( k3_enumset1 @ X25 @ X24 @ X23 @ X22 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 @ X2 ) ) ),
    inference('sup-',[status(thm)],['15','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','21'])).

thf('23',plain,(
    ~ ( zip_tseitin_0 @ ( k1_funct_1 @ sk_D @ sk_C ) @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['12','22'])).

thf('24',plain,
    ( ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B ) ),
    inference('sup-',[status(thm)],['0','23'])).

thf('25',plain,
    ( ( k1_funct_1 @ sk_D @ sk_C )
    = sk_B ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ( k1_funct_1 @ sk_D @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('27',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.B1lyM1vBln
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:46:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 69 iterations in 0.032s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.19/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.48  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.48  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.19/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.48  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o).
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.48  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.19/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.48  thf(d3_enumset1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.19/0.48     ( ( ( F ) = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) <=>
% 0.19/0.48       ( ![G:$i]:
% 0.19/0.48         ( ( r2_hidden @ G @ F ) <=>
% 0.19/0.48           ( ~( ( ( G ) != ( E ) ) & ( ( G ) != ( D ) ) & ( ( G ) != ( C ) ) & 
% 0.19/0.48                ( ( G ) != ( B ) ) & ( ( G ) != ( A ) ) ) ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, axiom,
% 0.19/0.48    (![G:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.19/0.48     ( ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) <=>
% 0.19/0.48       ( ( ( G ) != ( A ) ) & ( ( G ) != ( B ) ) & ( ( G ) != ( C ) ) & 
% 0.19/0.48         ( ( G ) != ( D ) ) & ( ( G ) != ( E ) ) ) ))).
% 0.19/0.48  thf('0', plain,
% 0.19/0.48      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.19/0.48         ((zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19)
% 0.19/0.48          | ((X14) = (X15))
% 0.19/0.48          | ((X14) = (X16))
% 0.19/0.48          | ((X14) = (X17))
% 0.19/0.48          | ((X14) = (X18))
% 0.19/0.48          | ((X14) = (X19)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t65_funct_2, conjecture,
% 0.19/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.48     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.19/0.48         ( m1_subset_1 @
% 0.19/0.48           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.19/0.48       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_1, negated_conjecture,
% 0.19/0.48    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.48        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.19/0.48            ( m1_subset_1 @
% 0.19/0.48              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.19/0.48          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.19/0.48  thf('1', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.19/0.48  thf('2', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_D @ 
% 0.19/0.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.19/0.48  thf(t7_funct_2, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.48     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.19/0.48         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.48       ( ( r2_hidden @ C @ A ) =>
% 0.19/0.48         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.19/0.48           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X29 @ X30)
% 0.19/0.48          | ((X31) = (k1_xboole_0))
% 0.19/0.48          | ~ (v1_funct_1 @ X32)
% 0.19/0.48          | ~ (v1_funct_2 @ X32 @ X30 @ X31)
% 0.19/0.48          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.19/0.48          | (r2_hidden @ (k1_funct_1 @ X32 @ X29) @ X31))),
% 0.19/0.48      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.19/0.48  thf('4', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.19/0.48          | ~ (v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))
% 0.19/0.48          | ~ (v1_funct_1 @ sk_D)
% 0.19/0.48          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.19/0.48          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.48  thf('5', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.19/0.48  thf('6', plain, ((v1_funct_1 @ sk_D)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.19/0.48  thf('7', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.19/0.48          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.19/0.48          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.19/0.48      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.19/0.48  thf(idempotence_k2_xboole_0, axiom,
% 0.19/0.48    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.19/0.48  thf('8', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.19/0.48      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.19/0.48  thf(t49_zfmisc_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.19/0.48  thf('9', plain,
% 0.19/0.48      (![X11 : $i, X12 : $i]:
% 0.19/0.48         ((k2_xboole_0 @ (k1_tarski @ X11) @ X12) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.19/0.48  thf('10', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.48  thf('11', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.19/0.48          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['7', '10'])).
% 0.19/0.48  thf('12', plain,
% 0.19/0.48      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_C) @ (k1_tarski @ sk_B))),
% 0.19/0.48      inference('sup-', [status(thm)], ['1', '11'])).
% 0.19/0.48  thf(t69_enumset1, axiom,
% 0.19/0.48    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.48  thf('13', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.19/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.48  thf(t70_enumset1, axiom,
% 0.19/0.48    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.19/0.48  thf('14', plain,
% 0.19/0.48      (![X2 : $i, X3 : $i]:
% 0.19/0.48         ((k1_enumset1 @ X2 @ X2 @ X3) = (k2_tarski @ X2 @ X3))),
% 0.19/0.48      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.19/0.48  thf(t71_enumset1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.19/0.48  thf('15', plain,
% 0.19/0.48      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.48         ((k2_enumset1 @ X4 @ X4 @ X5 @ X6) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 0.19/0.48      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.19/0.48  thf(t72_enumset1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.48     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.19/0.48  thf('16', plain,
% 0.19/0.48      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.19/0.48         ((k3_enumset1 @ X7 @ X7 @ X8 @ X9 @ X10)
% 0.19/0.48           = (k2_enumset1 @ X7 @ X8 @ X9 @ X10))),
% 0.19/0.48      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.19/0.48  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $i > $o).
% 0.19/0.48  thf(zf_stmt_3, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.19/0.48     ( ( ( F ) = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) <=>
% 0.19/0.48       ( ![G:$i]:
% 0.19/0.48         ( ( r2_hidden @ G @ F ) <=>
% 0.19/0.48           ( ~( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.19/0.48  thf('17', plain,
% 0.19/0.48      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X27 @ X26)
% 0.19/0.48          | ~ (zip_tseitin_0 @ X27 @ X21 @ X22 @ X23 @ X24 @ X25)
% 0.19/0.48          | ((X26) != (k3_enumset1 @ X25 @ X24 @ X23 @ X22 @ X21)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.19/0.48  thf('18', plain,
% 0.19/0.48      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X27 : $i]:
% 0.19/0.48         (~ (zip_tseitin_0 @ X27 @ X21 @ X22 @ X23 @ X24 @ X25)
% 0.19/0.48          | ~ (r2_hidden @ X27 @ (k3_enumset1 @ X25 @ X24 @ X23 @ X22 @ X21)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['17'])).
% 0.19/0.48  thf('19', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X4 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.19/0.48          | ~ (zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3))),
% 0.19/0.48      inference('sup-', [status(thm)], ['16', '18'])).
% 0.19/0.48  thf('20', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.19/0.48          | ~ (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 @ X2))),
% 0.19/0.48      inference('sup-', [status(thm)], ['15', '19'])).
% 0.19/0.48  thf('21', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.19/0.48          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1 @ X1))),
% 0.19/0.48      inference('sup-', [status(thm)], ['14', '20'])).
% 0.19/0.48  thf('22', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.19/0.48          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['13', '21'])).
% 0.19/0.48  thf('23', plain,
% 0.19/0.48      (~ (zip_tseitin_0 @ (k1_funct_1 @ sk_D @ sk_C) @ sk_B @ sk_B @ sk_B @ 
% 0.19/0.48          sk_B @ sk_B)),
% 0.19/0.48      inference('sup-', [status(thm)], ['12', '22'])).
% 0.19/0.48  thf('24', plain,
% 0.19/0.48      ((((k1_funct_1 @ sk_D @ sk_C) = (sk_B))
% 0.19/0.48        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B))
% 0.19/0.48        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B))
% 0.19/0.48        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B))
% 0.19/0.48        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['0', '23'])).
% 0.19/0.48  thf('25', plain, (((k1_funct_1 @ sk_D @ sk_C) = (sk_B))),
% 0.19/0.48      inference('simplify', [status(thm)], ['24'])).
% 0.19/0.48  thf('26', plain, (((k1_funct_1 @ sk_D @ sk_C) != (sk_B))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.19/0.48  thf('27', plain, ($false),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
