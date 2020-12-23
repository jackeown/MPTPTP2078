%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zu9VsRR1Ou

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:08 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :   42 (  42 expanded)
%              Number of leaves         :   22 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :  207 ( 207 expanded)
%              Number of equality atoms :   19 (  19 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t50_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t50_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ sk_C )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('2',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B_1 ) @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('3',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k2_tarski @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X53: $i,X54: $i] :
      ( ( k1_enumset1 @ X53 @ X53 @ X54 )
      = ( k2_tarski @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 @ X28 @ X29 )
      | ( r2_hidden @ X26 @ X30 )
      | ( X30
       != ( k1_enumset1 @ X29 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('9',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( r2_hidden @ X26 @ ( k1_enumset1 @ X29 @ X28 @ X27 ) )
      | ( zip_tseitin_0 @ X26 @ X27 @ X28 @ X29 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X22 != X21 )
      | ~ ( zip_tseitin_0 @ X22 @ X23 @ X24 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('12',plain,(
    ! [X21: $i,X23: $i,X24: $i] :
      ~ ( zip_tseitin_0 @ X21 @ X23 @ X24 @ X21 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','15'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('17',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('18',plain,(
    $false ),
    inference(demod,[status(thm)],['16','17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zu9VsRR1Ou
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:06:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.55/0.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.55/0.74  % Solved by: fo/fo7.sh
% 0.55/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.74  % done 811 iterations in 0.288s
% 0.55/0.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.55/0.74  % SZS output start Refutation
% 0.55/0.74  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.55/0.74  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.55/0.74  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.55/0.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.55/0.74  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.55/0.74  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.55/0.74  thf(sk_C_type, type, sk_C: $i).
% 0.55/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.55/0.74  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.55/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.55/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.74  thf(t50_zfmisc_1, conjecture,
% 0.55/0.74    (![A:$i,B:$i,C:$i]:
% 0.55/0.74     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 0.55/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.74    (~( ![A:$i,B:$i,C:$i]:
% 0.55/0.74        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 0.55/0.74    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 0.55/0.74  thf('0', plain,
% 0.55/0.74      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ sk_C) = (k1_xboole_0))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(t7_xboole_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.55/0.74  thf('1', plain,
% 0.55/0.74      (![X13 : $i, X14 : $i]: (r1_tarski @ X13 @ (k2_xboole_0 @ X13 @ X14))),
% 0.55/0.74      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.55/0.74  thf('2', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_B_1) @ k1_xboole_0)),
% 0.55/0.74      inference('sup+', [status(thm)], ['0', '1'])).
% 0.55/0.74  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.55/0.74  thf('3', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.55/0.74      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.55/0.74  thf(d10_xboole_0, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.55/0.74  thf('4', plain,
% 0.55/0.74      (![X5 : $i, X7 : $i]:
% 0.55/0.74         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 0.55/0.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.55/0.74  thf('5', plain,
% 0.55/0.74      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['3', '4'])).
% 0.55/0.74  thf('6', plain, (((k2_tarski @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.55/0.74      inference('sup-', [status(thm)], ['2', '5'])).
% 0.55/0.74  thf(t70_enumset1, axiom,
% 0.55/0.74    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.55/0.74  thf('7', plain,
% 0.55/0.74      (![X53 : $i, X54 : $i]:
% 0.55/0.74         ((k1_enumset1 @ X53 @ X53 @ X54) = (k2_tarski @ X53 @ X54))),
% 0.55/0.74      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.55/0.74  thf(d1_enumset1, axiom,
% 0.55/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.74     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.55/0.74       ( ![E:$i]:
% 0.55/0.74         ( ( r2_hidden @ E @ D ) <=>
% 0.55/0.74           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.55/0.74  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.55/0.74  thf(zf_stmt_2, axiom,
% 0.55/0.74    (![E:$i,C:$i,B:$i,A:$i]:
% 0.55/0.74     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.55/0.74       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.55/0.74  thf(zf_stmt_3, axiom,
% 0.55/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.74     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.55/0.74       ( ![E:$i]:
% 0.55/0.74         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.55/0.74  thf('8', plain,
% 0.55/0.74      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.55/0.74         ((zip_tseitin_0 @ X26 @ X27 @ X28 @ X29)
% 0.55/0.74          | (r2_hidden @ X26 @ X30)
% 0.55/0.74          | ((X30) != (k1_enumset1 @ X29 @ X28 @ X27)))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.55/0.74  thf('9', plain,
% 0.55/0.74      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.55/0.74         ((r2_hidden @ X26 @ (k1_enumset1 @ X29 @ X28 @ X27))
% 0.55/0.74          | (zip_tseitin_0 @ X26 @ X27 @ X28 @ X29))),
% 0.55/0.74      inference('simplify', [status(thm)], ['8'])).
% 0.55/0.74  thf('10', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.74         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.55/0.74          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.55/0.74      inference('sup+', [status(thm)], ['7', '9'])).
% 0.55/0.74  thf('11', plain,
% 0.55/0.74      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.55/0.74         (((X22) != (X21)) | ~ (zip_tseitin_0 @ X22 @ X23 @ X24 @ X21))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.55/0.74  thf('12', plain,
% 0.55/0.74      (![X21 : $i, X23 : $i, X24 : $i]:
% 0.55/0.74         ~ (zip_tseitin_0 @ X21 @ X23 @ X24 @ X21)),
% 0.55/0.74      inference('simplify', [status(thm)], ['11'])).
% 0.55/0.74  thf('13', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.55/0.74      inference('sup-', [status(thm)], ['10', '12'])).
% 0.55/0.74  thf(d1_xboole_0, axiom,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.55/0.74  thf('14', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.55/0.74      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.55/0.74  thf('15', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X1 @ X0))),
% 0.55/0.74      inference('sup-', [status(thm)], ['13', '14'])).
% 0.55/0.74  thf('16', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.55/0.74      inference('sup-', [status(thm)], ['6', '15'])).
% 0.55/0.74  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.55/0.74  thf('17', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.55/0.74      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.55/0.74  thf('18', plain, ($false), inference('demod', [status(thm)], ['16', '17'])).
% 0.55/0.74  
% 0.55/0.74  % SZS output end Refutation
% 0.55/0.74  
% 0.55/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
