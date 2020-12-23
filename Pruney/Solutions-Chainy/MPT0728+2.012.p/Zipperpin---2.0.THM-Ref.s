%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yn3mh3FIrn

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   34 (  34 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    8
%              Number of atoms          :  220 ( 220 expanded)
%              Number of equality atoms :   20 (  20 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

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
    ! [X23: $i] :
      ( ( k1_ordinal1 @ X23 )
      = ( k2_xboole_0 @ X23 @ ( k1_tarski @ X23 ) ) ) ),
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

thf(t77_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_enumset1 @ A @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_enumset1 @ X7 @ X7 @ X7 @ X8 )
      = ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t77_enumset1])).

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

thf('4',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 @ X19 )
      | ( r2_hidden @ X15 @ X20 )
      | ( X20
       != ( k2_enumset1 @ X19 @ X18 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('5',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ X15 @ ( k2_enumset1 @ X19 @ X18 @ X17 @ X16 ) )
      | ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 @ X19 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X10 != X9 )
      | ~ ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X13 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
    ! [X9: $i,X11: $i,X12: $i,X13: $i] :
      ~ ( zip_tseitin_0 @ X9 @ X11 @ X12 @ X13 @ X9 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','9'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','13'])).

thf('15',plain,(
    $false ),
    inference(demod,[status(thm)],['0','14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yn3mh3FIrn
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:38:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.45  % Solved by: fo/fo7.sh
% 0.20/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.45  % done 38 iterations in 0.037s
% 0.20/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.45  % SZS output start Refutation
% 0.20/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.45  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.20/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.45  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.45  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.45  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.45  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.20/0.45  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.20/0.45  thf(t10_ordinal1, conjecture,
% 0.20/0.45    (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.20/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.45    (~( ![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )),
% 0.20/0.45    inference('cnf.neg', [status(esa)], [t10_ordinal1])).
% 0.20/0.45  thf('0', plain, (~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf(d1_ordinal1, axiom,
% 0.20/0.45    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.20/0.45  thf('1', plain,
% 0.20/0.45      (![X23 : $i]:
% 0.20/0.45         ((k1_ordinal1 @ X23) = (k2_xboole_0 @ X23 @ (k1_tarski @ X23)))),
% 0.20/0.45      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.20/0.45  thf(t69_enumset1, axiom,
% 0.20/0.45    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.45  thf('2', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.20/0.45      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.45  thf(t77_enumset1, axiom,
% 0.20/0.45    (![A:$i,B:$i]: ( ( k2_enumset1 @ A @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.45  thf('3', plain,
% 0.20/0.45      (![X7 : $i, X8 : $i]:
% 0.20/0.45         ((k2_enumset1 @ X7 @ X7 @ X7 @ X8) = (k2_tarski @ X7 @ X8))),
% 0.20/0.45      inference('cnf', [status(esa)], [t77_enumset1])).
% 0.20/0.45  thf(d2_enumset1, axiom,
% 0.20/0.45    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.45     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.20/0.45       ( ![F:$i]:
% 0.20/0.45         ( ( r2_hidden @ F @ E ) <=>
% 0.20/0.45           ( ~( ( ( F ) != ( D ) ) & ( ( F ) != ( C ) ) & ( ( F ) != ( B ) ) & 
% 0.20/0.45                ( ( F ) != ( A ) ) ) ) ) ) ))).
% 0.20/0.45  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.20/0.45  thf(zf_stmt_2, axiom,
% 0.20/0.45    (![F:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.20/0.45     ( ( zip_tseitin_0 @ F @ D @ C @ B @ A ) <=>
% 0.20/0.45       ( ( ( F ) != ( A ) ) & ( ( F ) != ( B ) ) & ( ( F ) != ( C ) ) & 
% 0.20/0.45         ( ( F ) != ( D ) ) ) ))).
% 0.20/0.45  thf(zf_stmt_3, axiom,
% 0.20/0.45    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.45     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.20/0.45       ( ![F:$i]:
% 0.20/0.45         ( ( r2_hidden @ F @ E ) <=> ( ~( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) ) ))).
% 0.20/0.45  thf('4', plain,
% 0.20/0.45      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.45         ((zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 @ X19)
% 0.20/0.45          | (r2_hidden @ X15 @ X20)
% 0.20/0.45          | ((X20) != (k2_enumset1 @ X19 @ X18 @ X17 @ X16)))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.45  thf('5', plain,
% 0.20/0.45      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.45         ((r2_hidden @ X15 @ (k2_enumset1 @ X19 @ X18 @ X17 @ X16))
% 0.20/0.45          | (zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 @ X19))),
% 0.20/0.45      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.45  thf('6', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.45         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.20/0.45          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1))),
% 0.20/0.45      inference('sup+', [status(thm)], ['3', '5'])).
% 0.20/0.45  thf('7', plain,
% 0.20/0.45      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.45         (((X10) != (X9)) | ~ (zip_tseitin_0 @ X10 @ X11 @ X12 @ X13 @ X9))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.45  thf('8', plain,
% 0.20/0.45      (![X9 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.45         ~ (zip_tseitin_0 @ X9 @ X11 @ X12 @ X13 @ X9)),
% 0.20/0.45      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.45  thf('9', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.20/0.45      inference('sup-', [status(thm)], ['6', '8'])).
% 0.20/0.45  thf('10', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.45      inference('sup+', [status(thm)], ['2', '9'])).
% 0.20/0.45  thf(d3_xboole_0, axiom,
% 0.20/0.45    (![A:$i,B:$i,C:$i]:
% 0.20/0.45     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.20/0.45       ( ![D:$i]:
% 0.20/0.45         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.45           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.20/0.45  thf('11', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.45         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.45          | (r2_hidden @ X0 @ X2)
% 0.20/0.45          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.20/0.45      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.20/0.45  thf('12', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.20/0.45         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.45      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.45  thf('13', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['10', '12'])).
% 0.20/0.45  thf('14', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_ordinal1 @ X0))),
% 0.20/0.45      inference('sup+', [status(thm)], ['1', '13'])).
% 0.20/0.45  thf('15', plain, ($false), inference('demod', [status(thm)], ['0', '14'])).
% 0.20/0.45  
% 0.20/0.45  % SZS output end Refutation
% 0.20/0.45  
% 0.20/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
