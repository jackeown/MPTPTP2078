%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3mtucoO1hO

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 (  38 expanded)
%              Number of leaves         :   19 (  19 expanded)
%              Depth                    :    9
%              Number of atoms          :  245 ( 245 expanded)
%              Number of equality atoms :   22 (  22 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

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
    ! [X26: $i] :
      ( ( k1_ordinal1 @ X26 )
      = ( k2_xboole_0 @ X26 @ ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k1_enumset1 @ X7 @ X7 @ X8 )
      = ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k2_enumset1 @ X9 @ X9 @ X10 @ X11 )
      = ( k1_enumset1 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

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

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [F: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ D @ C @ B @ A )
    <=> ( ( F != A )
        & ( F != B )
        & ( F != C )
        & ( F != D ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( E
        = ( k2_enumset1 @ A @ B @ C @ D ) )
    <=> ! [F: $i] :
          ( ( r2_hidden @ F @ E )
        <=> ~ ( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 @ X22 )
      | ( r2_hidden @ X18 @ X23 )
      | ( X23
       != ( k2_enumset1 @ X22 @ X21 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('6',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ X18 @ ( k2_enumset1 @ X22 @ X21 @ X20 @ X19 ) )
      | ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 @ X22 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X13 != X12 )
      | ~ ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('9',plain,(
    ! [X12: $i,X14: $i,X15: $i,X16: $i] :
      ~ ( zip_tseitin_0 @ X12 @ X14 @ X15 @ X16 @ X12 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X0 @ ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','11'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','15'])).

thf('17',plain,(
    $false ),
    inference(demod,[status(thm)],['0','16'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3mtucoO1hO
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:19:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 40 iterations in 0.047s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.21/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.50  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.21/0.50  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.21/0.50  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.50  thf(t10_ordinal1, conjecture,
% 0.21/0.50    (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t10_ordinal1])).
% 0.21/0.50  thf('0', plain, (~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(d1_ordinal1, axiom,
% 0.21/0.50    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (![X26 : $i]:
% 0.21/0.50         ((k1_ordinal1 @ X26) = (k2_xboole_0 @ X26 @ (k1_tarski @ X26)))),
% 0.21/0.50      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.21/0.50  thf(t69_enumset1, axiom,
% 0.21/0.50    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.50  thf('2', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.50  thf(t70_enumset1, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X7 : $i, X8 : $i]:
% 0.21/0.50         ((k1_enumset1 @ X7 @ X7 @ X8) = (k2_tarski @ X7 @ X8))),
% 0.21/0.50      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.50  thf(t71_enumset1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.50         ((k2_enumset1 @ X9 @ X9 @ X10 @ X11) = (k1_enumset1 @ X9 @ X10 @ X11))),
% 0.21/0.50      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.21/0.50  thf(d2_enumset1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.50     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.21/0.50       ( ![F:$i]:
% 0.21/0.50         ( ( r2_hidden @ F @ E ) <=>
% 0.21/0.50           ( ~( ( ( F ) != ( D ) ) & ( ( F ) != ( C ) ) & ( ( F ) != ( B ) ) & 
% 0.21/0.50                ( ( F ) != ( A ) ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.21/0.50  thf(zf_stmt_2, axiom,
% 0.21/0.50    (![F:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.21/0.50     ( ( zip_tseitin_0 @ F @ D @ C @ B @ A ) <=>
% 0.21/0.50       ( ( ( F ) != ( A ) ) & ( ( F ) != ( B ) ) & ( ( F ) != ( C ) ) & 
% 0.21/0.50         ( ( F ) != ( D ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_3, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.50     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.21/0.50       ( ![F:$i]:
% 0.21/0.50         ( ( r2_hidden @ F @ E ) <=> ( ~( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) ) ))).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.50         ((zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 @ X22)
% 0.21/0.50          | (r2_hidden @ X18 @ X23)
% 0.21/0.50          | ((X23) != (k2_enumset1 @ X22 @ X21 @ X20 @ X19)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.50         ((r2_hidden @ X18 @ (k2_enumset1 @ X22 @ X21 @ X20 @ X19))
% 0.21/0.50          | (zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 @ X22))),
% 0.21/0.50      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.50         ((r2_hidden @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.21/0.50          | (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2))),
% 0.21/0.50      inference('sup+', [status(thm)], ['4', '6'])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.50         (((X13) != (X12)) | ~ (zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 @ X12))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (![X12 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.50         ~ (zip_tseitin_0 @ X12 @ X14 @ X15 @ X16 @ X12)),
% 0.21/0.50      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (r2_hidden @ X0 @ (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.21/0.50      inference('sup-', [status(thm)], ['7', '9'])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['3', '10'])).
% 0.21/0.50  thf('12', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['2', '11'])).
% 0.21/0.50  thf(d3_xboole_0, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.21/0.50       ( ![D:$i]:
% 0.21/0.50         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.50           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.50          | (r2_hidden @ X0 @ X2)
% 0.21/0.50          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.21/0.50         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.21/0.50      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['12', '14'])).
% 0.21/0.50  thf('16', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_ordinal1 @ X0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['1', '15'])).
% 0.21/0.50  thf('17', plain, ($false), inference('demod', [status(thm)], ['0', '16'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
