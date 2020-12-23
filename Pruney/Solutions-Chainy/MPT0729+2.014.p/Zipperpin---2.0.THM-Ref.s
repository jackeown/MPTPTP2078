%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mUOkMBoiiU

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:42 EST 2020

% Result     : Theorem 0.82s
% Output     : Refutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :   60 (  84 expanded)
%              Number of leaves         :   22 (  33 expanded)
%              Depth                    :   14
%              Number of atoms          :  430 ( 665 expanded)
%              Number of equality atoms :   48 (  77 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

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
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 @ X21 )
      | ( X17 = X18 )
      | ( X17 = X19 )
      | ( X17 = X20 )
      | ( X17 = X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('1',plain,(
    ! [X31: $i] :
      ( r2_hidden @ X31 @ ( k1_ordinal1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf(t12_ordinal1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k1_ordinal1 @ A )
        = ( k1_ordinal1 @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k1_ordinal1 @ A )
          = ( k1_ordinal1 @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_ordinal1])).

thf('2',plain,
    ( ( k1_ordinal1 @ sk_A )
    = ( k1_ordinal1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('3',plain,(
    ! [X30: $i] :
      ( ( k1_ordinal1 @ X30 )
      = ( k2_xboole_0 @ X30 @ ( k1_tarski @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('5',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_ordinal1 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','6'])).

thf('8',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 @ X21 )
      | ( X17 = X18 )
      | ( X17 = X19 )
      | ( X17 = X20 )
      | ( X17 = X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k1_ordinal1 @ sk_A )
    = ( k1_ordinal1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('11',plain,(
    ! [X31: $i] :
      ( r2_hidden @ X31 @ ( k1_ordinal1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('12',plain,(
    r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('14',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_enumset1 @ X9 @ X9 @ X10 )
      = ( k2_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('16',plain,(
    ! [X8: $i] :
      ( ( k2_tarski @ X8 @ X8 )
      = ( k1_tarski @ X8 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('18',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X11 @ X11 @ X12 @ X13 )
      = ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ),
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

thf('19',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X28 @ X27 )
      | ~ ( zip_tseitin_0 @ X28 @ X23 @ X24 @ X25 @ X26 )
      | ( X27
       != ( k2_enumset1 @ X26 @ X25 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('20',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X23 @ X24 @ X25 @ X26 )
      | ~ ( r2_hidden @ X28 @ ( k2_enumset1 @ X26 @ X25 @ X24 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','21'])).

thf('23',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['14','22'])).

thf('24',plain,
    ( ( sk_B = sk_A )
    | ( sk_B = sk_A )
    | ( sk_B = sk_A )
    | ( sk_B = sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','23'])).

thf('25',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( sk_B = sk_A ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('27',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('29',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['8','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','21'])).

thf('32',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['0','32'])).

thf('34',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('36',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['34','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mUOkMBoiiU
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:43:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.82/1.04  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.82/1.04  % Solved by: fo/fo7.sh
% 0.82/1.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.82/1.04  % done 1494 iterations in 0.588s
% 0.82/1.04  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.82/1.04  % SZS output start Refutation
% 0.82/1.04  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.82/1.04  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.82/1.04  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.82/1.04  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.82/1.04  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.82/1.04  thf(sk_B_type, type, sk_B: $i).
% 0.82/1.04  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.82/1.04  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.82/1.04  thf(sk_A_type, type, sk_A: $i).
% 0.82/1.04  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.82/1.04  thf(d2_enumset1, axiom,
% 0.82/1.04    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.82/1.04     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.82/1.04       ( ![F:$i]:
% 0.82/1.04         ( ( r2_hidden @ F @ E ) <=>
% 0.82/1.04           ( ~( ( ( F ) != ( D ) ) & ( ( F ) != ( C ) ) & ( ( F ) != ( B ) ) & 
% 0.82/1.04                ( ( F ) != ( A ) ) ) ) ) ) ))).
% 0.82/1.04  thf(zf_stmt_0, axiom,
% 0.82/1.04    (![F:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.82/1.04     ( ( zip_tseitin_0 @ F @ D @ C @ B @ A ) <=>
% 0.82/1.04       ( ( ( F ) != ( A ) ) & ( ( F ) != ( B ) ) & ( ( F ) != ( C ) ) & 
% 0.82/1.04         ( ( F ) != ( D ) ) ) ))).
% 0.82/1.04  thf('0', plain,
% 0.82/1.04      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.82/1.04         ((zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 @ X21)
% 0.82/1.04          | ((X17) = (X18))
% 0.82/1.04          | ((X17) = (X19))
% 0.82/1.04          | ((X17) = (X20))
% 0.82/1.04          | ((X17) = (X21)))),
% 0.82/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.04  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.82/1.04  thf('1', plain, (![X31 : $i]: (r2_hidden @ X31 @ (k1_ordinal1 @ X31))),
% 0.82/1.04      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.82/1.04  thf(t12_ordinal1, conjecture,
% 0.82/1.04    (![A:$i,B:$i]:
% 0.82/1.04     ( ( ( k1_ordinal1 @ A ) = ( k1_ordinal1 @ B ) ) => ( ( A ) = ( B ) ) ))).
% 0.82/1.04  thf(zf_stmt_1, negated_conjecture,
% 0.82/1.04    (~( ![A:$i,B:$i]:
% 0.82/1.04        ( ( ( k1_ordinal1 @ A ) = ( k1_ordinal1 @ B ) ) => ( ( A ) = ( B ) ) ) )),
% 0.82/1.04    inference('cnf.neg', [status(esa)], [t12_ordinal1])).
% 0.82/1.04  thf('2', plain, (((k1_ordinal1 @ sk_A) = (k1_ordinal1 @ sk_B))),
% 0.82/1.04      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.82/1.04  thf(d1_ordinal1, axiom,
% 0.82/1.04    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.82/1.04  thf('3', plain,
% 0.82/1.04      (![X30 : $i]:
% 0.82/1.04         ((k1_ordinal1 @ X30) = (k2_xboole_0 @ X30 @ (k1_tarski @ X30)))),
% 0.82/1.04      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.82/1.04  thf(d3_xboole_0, axiom,
% 0.82/1.04    (![A:$i,B:$i,C:$i]:
% 0.82/1.04     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.82/1.04       ( ![D:$i]:
% 0.82/1.04         ( ( r2_hidden @ D @ C ) <=>
% 0.82/1.04           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.82/1.04  thf('4', plain,
% 0.82/1.04      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.82/1.04         (~ (r2_hidden @ X6 @ X4)
% 0.82/1.04          | (r2_hidden @ X6 @ X5)
% 0.82/1.04          | (r2_hidden @ X6 @ X3)
% 0.82/1.04          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.82/1.04      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.82/1.04  thf('5', plain,
% 0.82/1.04      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.82/1.04         ((r2_hidden @ X6 @ X3)
% 0.82/1.04          | (r2_hidden @ X6 @ X5)
% 0.82/1.04          | ~ (r2_hidden @ X6 @ (k2_xboole_0 @ X5 @ X3)))),
% 0.82/1.04      inference('simplify', [status(thm)], ['4'])).
% 0.82/1.04  thf('6', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i]:
% 0.82/1.04         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.82/1.04          | (r2_hidden @ X1 @ X0)
% 0.82/1.04          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.82/1.04      inference('sup-', [status(thm)], ['3', '5'])).
% 0.82/1.04  thf('7', plain,
% 0.82/1.04      (![X0 : $i]:
% 0.82/1.04         (~ (r2_hidden @ X0 @ (k1_ordinal1 @ sk_A))
% 0.82/1.04          | (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.82/1.04          | (r2_hidden @ X0 @ sk_B))),
% 0.82/1.04      inference('sup-', [status(thm)], ['2', '6'])).
% 0.82/1.04  thf('8', plain,
% 0.82/1.04      (((r2_hidden @ sk_A @ sk_B) | (r2_hidden @ sk_A @ (k1_tarski @ sk_B)))),
% 0.82/1.04      inference('sup-', [status(thm)], ['1', '7'])).
% 0.82/1.04  thf('9', plain,
% 0.82/1.04      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.82/1.04         ((zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 @ X21)
% 0.82/1.04          | ((X17) = (X18))
% 0.82/1.04          | ((X17) = (X19))
% 0.82/1.04          | ((X17) = (X20))
% 0.82/1.04          | ((X17) = (X21)))),
% 0.82/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.04  thf('10', plain, (((k1_ordinal1 @ sk_A) = (k1_ordinal1 @ sk_B))),
% 0.82/1.04      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.82/1.04  thf('11', plain, (![X31 : $i]: (r2_hidden @ X31 @ (k1_ordinal1 @ X31))),
% 0.82/1.04      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.82/1.04  thf('12', plain, ((r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))),
% 0.82/1.04      inference('sup+', [status(thm)], ['10', '11'])).
% 0.82/1.04  thf('13', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i]:
% 0.82/1.04         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.82/1.04          | (r2_hidden @ X1 @ X0)
% 0.82/1.04          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.82/1.04      inference('sup-', [status(thm)], ['3', '5'])).
% 0.82/1.04  thf('14', plain,
% 0.82/1.04      (((r2_hidden @ sk_B @ (k1_tarski @ sk_A)) | (r2_hidden @ sk_B @ sk_A))),
% 0.82/1.04      inference('sup-', [status(thm)], ['12', '13'])).
% 0.82/1.04  thf(t70_enumset1, axiom,
% 0.82/1.04    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.82/1.04  thf('15', plain,
% 0.82/1.04      (![X9 : $i, X10 : $i]:
% 0.82/1.04         ((k1_enumset1 @ X9 @ X9 @ X10) = (k2_tarski @ X9 @ X10))),
% 0.82/1.04      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.82/1.04  thf(t69_enumset1, axiom,
% 0.82/1.04    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.82/1.04  thf('16', plain, (![X8 : $i]: ((k2_tarski @ X8 @ X8) = (k1_tarski @ X8))),
% 0.82/1.04      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.82/1.04  thf('17', plain,
% 0.82/1.04      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.82/1.04      inference('sup+', [status(thm)], ['15', '16'])).
% 0.82/1.04  thf(t71_enumset1, axiom,
% 0.82/1.04    (![A:$i,B:$i,C:$i]:
% 0.82/1.04     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.82/1.04  thf('18', plain,
% 0.82/1.04      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.82/1.04         ((k2_enumset1 @ X11 @ X11 @ X12 @ X13)
% 0.82/1.04           = (k1_enumset1 @ X11 @ X12 @ X13))),
% 0.82/1.04      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.82/1.04  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.82/1.04  thf(zf_stmt_3, axiom,
% 0.82/1.04    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.82/1.04     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.82/1.04       ( ![F:$i]:
% 0.82/1.04         ( ( r2_hidden @ F @ E ) <=> ( ~( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) ) ))).
% 0.82/1.04  thf('19', plain,
% 0.82/1.04      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.82/1.04         (~ (r2_hidden @ X28 @ X27)
% 0.82/1.04          | ~ (zip_tseitin_0 @ X28 @ X23 @ X24 @ X25 @ X26)
% 0.82/1.04          | ((X27) != (k2_enumset1 @ X26 @ X25 @ X24 @ X23)))),
% 0.82/1.04      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.82/1.04  thf('20', plain,
% 0.82/1.04      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X28 : $i]:
% 0.82/1.04         (~ (zip_tseitin_0 @ X28 @ X23 @ X24 @ X25 @ X26)
% 0.82/1.04          | ~ (r2_hidden @ X28 @ (k2_enumset1 @ X26 @ X25 @ X24 @ X23)))),
% 0.82/1.04      inference('simplify', [status(thm)], ['19'])).
% 0.82/1.04  thf('21', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.82/1.04         (~ (r2_hidden @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.82/1.04          | ~ (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2))),
% 0.82/1.04      inference('sup-', [status(thm)], ['18', '20'])).
% 0.82/1.04  thf('22', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i]:
% 0.82/1.04         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.82/1.04          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0))),
% 0.82/1.04      inference('sup-', [status(thm)], ['17', '21'])).
% 0.82/1.04  thf('23', plain,
% 0.82/1.04      (((r2_hidden @ sk_B @ sk_A)
% 0.82/1.04        | ~ (zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A @ sk_A))),
% 0.82/1.04      inference('sup-', [status(thm)], ['14', '22'])).
% 0.82/1.04  thf('24', plain,
% 0.82/1.04      ((((sk_B) = (sk_A))
% 0.82/1.04        | ((sk_B) = (sk_A))
% 0.82/1.04        | ((sk_B) = (sk_A))
% 0.82/1.04        | ((sk_B) = (sk_A))
% 0.82/1.04        | (r2_hidden @ sk_B @ sk_A))),
% 0.82/1.04      inference('sup-', [status(thm)], ['9', '23'])).
% 0.82/1.04  thf('25', plain, (((r2_hidden @ sk_B @ sk_A) | ((sk_B) = (sk_A)))),
% 0.82/1.04      inference('simplify', [status(thm)], ['24'])).
% 0.82/1.04  thf('26', plain, (((sk_A) != (sk_B))),
% 0.82/1.04      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.82/1.04  thf('27', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.82/1.04      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 0.82/1.04  thf(antisymmetry_r2_hidden, axiom,
% 0.82/1.04    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.82/1.04  thf('28', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.82/1.04      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.82/1.04  thf('29', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.82/1.04      inference('sup-', [status(thm)], ['27', '28'])).
% 0.82/1.04  thf('30', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.82/1.04      inference('clc', [status(thm)], ['8', '29'])).
% 0.82/1.04  thf('31', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i]:
% 0.82/1.04         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.82/1.04          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0))),
% 0.82/1.04      inference('sup-', [status(thm)], ['17', '21'])).
% 0.82/1.04  thf('32', plain, (~ (zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_B)),
% 0.82/1.04      inference('sup-', [status(thm)], ['30', '31'])).
% 0.82/1.04  thf('33', plain,
% 0.82/1.04      ((((sk_A) = (sk_B))
% 0.82/1.04        | ((sk_A) = (sk_B))
% 0.82/1.04        | ((sk_A) = (sk_B))
% 0.82/1.04        | ((sk_A) = (sk_B)))),
% 0.82/1.04      inference('sup-', [status(thm)], ['0', '32'])).
% 0.82/1.04  thf('34', plain, (((sk_A) = (sk_B))),
% 0.82/1.04      inference('simplify', [status(thm)], ['33'])).
% 0.82/1.04  thf('35', plain, (((sk_A) != (sk_B))),
% 0.82/1.04      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.82/1.04  thf('36', plain, ($false),
% 0.82/1.04      inference('simplify_reflect-', [status(thm)], ['34', '35'])).
% 0.82/1.04  
% 0.82/1.04  % SZS output end Refutation
% 0.82/1.04  
% 0.82/1.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
