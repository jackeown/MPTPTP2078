%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HPTY3t0mZ0

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:39 EST 2020

% Result     : Theorem 0.82s
% Output     : Refutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :   42 (  42 expanded)
%              Number of leaves         :   21 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :  296 ( 296 expanded)
%              Number of equality atoms :   27 (  27 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(t10_ordinal1,conjecture,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t10_ordinal1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('1',plain,(
    ! [X34: $i] :
      ( ( k1_ordinal1 @ X34 )
      = ( k2_xboole_0 @ X34 @ ( k1_tarski @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k1_enumset1 @ X7 @ X7 @ X8 )
      = ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('3',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k2_enumset1 @ X9 @ X9 @ X10 @ X11 )
      = ( k1_enumset1 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k3_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15 )
      = ( k2_enumset1 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

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

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [G: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A )
    <=> ( ( G != A )
        & ( G != B )
        & ( G != C )
        & ( G != D )
        & ( G != E ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( F
        = ( k3_enumset1 @ A @ B @ C @ D @ E ) )
    <=> ! [G: $i] :
          ( ( r2_hidden @ G @ F )
        <=> ~ ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 )
      | ( r2_hidden @ X25 @ X31 )
      | ( X31
       != ( k3_enumset1 @ X30 @ X29 @ X28 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('8',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( r2_hidden @ X25 @ ( k3_enumset1 @ X30 @ X29 @ X28 @ X27 @ X26 ) )
      | ( zip_tseitin_0 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( X19 != X18 )
      | ~ ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 @ X23 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('11',plain,(
    ! [X18: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ~ ( zip_tseitin_0 @ X18 @ X20 @ X21 @ X22 @ X23 @ X18 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','13'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','17'])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['0','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HPTY3t0mZ0
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:22:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.82/1.02  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.82/1.02  % Solved by: fo/fo7.sh
% 0.82/1.02  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.82/1.02  % done 485 iterations in 0.567s
% 0.82/1.02  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.82/1.02  % SZS output start Refutation
% 0.82/1.02  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.82/1.02  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.82/1.02  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.82/1.02  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.82/1.02  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o).
% 0.82/1.02  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.82/1.02  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.82/1.02  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.82/1.02  thf(sk_A_type, type, sk_A: $i).
% 0.82/1.02  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.82/1.02  thf(t10_ordinal1, conjecture,
% 0.82/1.02    (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.82/1.02  thf(zf_stmt_0, negated_conjecture,
% 0.82/1.02    (~( ![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )),
% 0.82/1.02    inference('cnf.neg', [status(esa)], [t10_ordinal1])).
% 0.82/1.02  thf('0', plain, (~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A))),
% 0.82/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.02  thf(d1_ordinal1, axiom,
% 0.82/1.02    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.82/1.02  thf('1', plain,
% 0.82/1.02      (![X34 : $i]:
% 0.82/1.02         ((k1_ordinal1 @ X34) = (k2_xboole_0 @ X34 @ (k1_tarski @ X34)))),
% 0.82/1.02      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.82/1.02  thf(t70_enumset1, axiom,
% 0.82/1.02    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.82/1.02  thf('2', plain,
% 0.82/1.02      (![X7 : $i, X8 : $i]:
% 0.82/1.02         ((k1_enumset1 @ X7 @ X7 @ X8) = (k2_tarski @ X7 @ X8))),
% 0.82/1.02      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.82/1.02  thf(t69_enumset1, axiom,
% 0.82/1.02    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.82/1.02  thf('3', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.82/1.02      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.82/1.02  thf('4', plain,
% 0.82/1.02      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.82/1.02      inference('sup+', [status(thm)], ['2', '3'])).
% 0.82/1.02  thf(t71_enumset1, axiom,
% 0.82/1.02    (![A:$i,B:$i,C:$i]:
% 0.82/1.02     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.82/1.02  thf('5', plain,
% 0.82/1.02      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.82/1.02         ((k2_enumset1 @ X9 @ X9 @ X10 @ X11) = (k1_enumset1 @ X9 @ X10 @ X11))),
% 0.82/1.02      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.82/1.02  thf(t72_enumset1, axiom,
% 0.82/1.02    (![A:$i,B:$i,C:$i,D:$i]:
% 0.82/1.02     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.82/1.02  thf('6', plain,
% 0.82/1.02      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.82/1.02         ((k3_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15)
% 0.82/1.02           = (k2_enumset1 @ X12 @ X13 @ X14 @ X15))),
% 0.82/1.02      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.82/1.02  thf(d3_enumset1, axiom,
% 0.82/1.02    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.82/1.02     ( ( ( F ) = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) <=>
% 0.82/1.02       ( ![G:$i]:
% 0.82/1.02         ( ( r2_hidden @ G @ F ) <=>
% 0.82/1.02           ( ~( ( ( G ) != ( E ) ) & ( ( G ) != ( D ) ) & ( ( G ) != ( C ) ) & 
% 0.82/1.02                ( ( G ) != ( B ) ) & ( ( G ) != ( A ) ) ) ) ) ) ))).
% 0.82/1.02  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $i > $o).
% 0.82/1.02  thf(zf_stmt_2, axiom,
% 0.82/1.02    (![G:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.82/1.02     ( ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) <=>
% 0.82/1.02       ( ( ( G ) != ( A ) ) & ( ( G ) != ( B ) ) & ( ( G ) != ( C ) ) & 
% 0.82/1.02         ( ( G ) != ( D ) ) & ( ( G ) != ( E ) ) ) ))).
% 0.82/1.02  thf(zf_stmt_3, axiom,
% 0.82/1.02    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.82/1.02     ( ( ( F ) = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) <=>
% 0.82/1.02       ( ![G:$i]:
% 0.82/1.02         ( ( r2_hidden @ G @ F ) <=>
% 0.82/1.02           ( ~( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.82/1.02  thf('7', plain,
% 0.82/1.02      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.82/1.02         ((zip_tseitin_0 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30)
% 0.82/1.02          | (r2_hidden @ X25 @ X31)
% 0.82/1.02          | ((X31) != (k3_enumset1 @ X30 @ X29 @ X28 @ X27 @ X26)))),
% 0.82/1.02      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.82/1.02  thf('8', plain,
% 0.82/1.02      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.82/1.02         ((r2_hidden @ X25 @ (k3_enumset1 @ X30 @ X29 @ X28 @ X27 @ X26))
% 0.82/1.02          | (zip_tseitin_0 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30))),
% 0.82/1.02      inference('simplify', [status(thm)], ['7'])).
% 0.82/1.02  thf('9', plain,
% 0.82/1.02      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.82/1.02         ((r2_hidden @ X4 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.82/1.02          | (zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3))),
% 0.82/1.02      inference('sup+', [status(thm)], ['6', '8'])).
% 0.82/1.02  thf('10', plain,
% 0.82/1.02      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.82/1.02         (((X19) != (X18))
% 0.82/1.02          | ~ (zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 @ X23 @ X18))),
% 0.82/1.02      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.82/1.02  thf('11', plain,
% 0.82/1.02      (![X18 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.82/1.02         ~ (zip_tseitin_0 @ X18 @ X20 @ X21 @ X22 @ X23 @ X18)),
% 0.82/1.02      inference('simplify', [status(thm)], ['10'])).
% 0.82/1.02  thf('12', plain,
% 0.82/1.02      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.82/1.02         (r2_hidden @ X0 @ (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.82/1.02      inference('sup-', [status(thm)], ['9', '11'])).
% 0.82/1.02  thf('13', plain,
% 0.82/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.02         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.82/1.02      inference('sup+', [status(thm)], ['5', '12'])).
% 0.82/1.02  thf('14', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.82/1.02      inference('sup+', [status(thm)], ['4', '13'])).
% 0.82/1.02  thf(d3_xboole_0, axiom,
% 0.82/1.02    (![A:$i,B:$i,C:$i]:
% 0.82/1.02     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.82/1.02       ( ![D:$i]:
% 0.82/1.02         ( ( r2_hidden @ D @ C ) <=>
% 0.82/1.02           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.82/1.02  thf('15', plain,
% 0.82/1.02      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.82/1.02         (~ (r2_hidden @ X0 @ X1)
% 0.82/1.02          | (r2_hidden @ X0 @ X2)
% 0.82/1.02          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.82/1.02      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.82/1.02  thf('16', plain,
% 0.82/1.02      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.82/1.02         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.82/1.02      inference('simplify', [status(thm)], ['15'])).
% 0.82/1.02  thf('17', plain,
% 0.82/1.02      (![X0 : $i, X1 : $i]:
% 0.82/1.02         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.82/1.02      inference('sup-', [status(thm)], ['14', '16'])).
% 0.82/1.02  thf('18', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_ordinal1 @ X0))),
% 0.82/1.02      inference('sup+', [status(thm)], ['1', '17'])).
% 0.82/1.02  thf('19', plain, ($false), inference('demod', [status(thm)], ['0', '18'])).
% 0.82/1.02  
% 0.82/1.02  % SZS output end Refutation
% 0.82/1.02  
% 0.82/1.03  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
