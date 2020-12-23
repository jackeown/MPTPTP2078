%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.I9qED0AYws

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   33 (  35 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    9
%              Number of atoms          :  264 ( 288 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(k2_setfam_1_type,type,(
    k2_setfam_1: $i > $i > $i )).

thf(t29_setfam_1,conjecture,(
    ! [A: $i] :
      ( r1_setfam_1 @ A @ ( k2_setfam_1 @ A @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( r1_setfam_1 @ A @ ( k2_setfam_1 @ A @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t29_setfam_1])).

thf('0',plain,(
    ~ ( r1_setfam_1 @ sk_A @ ( k2_setfam_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
    <=> ! [C: $i] :
          ~ ( ( r2_hidden @ C @ A )
            & ! [D: $i] :
                ~ ( ( r2_hidden @ D @ B )
                  & ( r1_tarski @ C @ D ) ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_setfam_1 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_setfam_1 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf(d4_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_setfam_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( ( r2_hidden @ E @ A )
              & ( r2_hidden @ F @ B )
              & ( D
                = ( k2_xboole_0 @ E @ F ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [F: $i,E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ D @ B @ A )
    <=> ( ( D
          = ( k2_xboole_0 @ E @ F ) )
        & ( r2_hidden @ F @ B )
        & ( r2_hidden @ E @ A ) ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X8 @ X7 @ X9 @ X10 @ X12 )
      | ~ ( r2_hidden @ X7 @ X12 )
      | ~ ( r2_hidden @ X8 @ X10 )
      | ( X9
       != ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('4',plain,(
    ! [X7: $i,X8: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X8 @ X10 )
      | ~ ( r2_hidden @ X7 @ X12 )
      | ( zip_tseitin_0 @ X8 @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) @ X10 @ X12 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ( zip_tseitin_0 @ ( sk_C @ X1 @ X0 ) @ X3 @ ( k2_xboole_0 @ X3 @ ( sk_C @ X1 @ X0 ) ) @ X0 @ X2 )
      | ~ ( r2_hidden @ X3 @ X2 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ( zip_tseitin_0 @ ( sk_C @ X3 @ X2 ) @ ( sk_C @ X1 @ X0 ) @ ( k2_xboole_0 @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X3 @ X2 ) ) @ X2 @ X0 )
      | ( r1_setfam_1 @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_setfam_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 @ X17 )
      | ( r2_hidden @ X15 @ X18 )
      | ( X18
       != ( k2_setfam_1 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('8',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X15 @ ( k2_setfam_1 @ X17 @ X16 ) )
      | ~ ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_setfam_1 @ X1 @ X2 )
      | ( r1_setfam_1 @ X0 @ X3 )
      | ( r2_hidden @ ( k2_xboole_0 @ ( sk_C @ X3 @ X0 ) @ ( sk_C @ X2 @ X1 ) ) @ ( k2_setfam_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('11',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r1_setfam_1 @ X4 @ X5 )
      | ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r1_tarski @ ( sk_C @ X5 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k2_xboole_0 @ ( sk_C @ X2 @ X1 ) @ X0 ) @ X2 )
      | ( r1_setfam_1 @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_setfam_1 @ X1 @ ( k2_setfam_1 @ X1 @ X0 ) )
      | ( r1_setfam_1 @ X0 @ X2 )
      | ( r1_setfam_1 @ X1 @ ( k2_setfam_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_setfam_1 @ X0 @ X2 )
      | ( r1_setfam_1 @ X1 @ ( k2_setfam_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_setfam_1 @ X0 @ ( k2_setfam_1 @ X0 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['14'])).

thf('16',plain,(
    $false ),
    inference(demod,[status(thm)],['0','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.I9qED0AYws
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:11:50 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 32 iterations in 0.036s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.49  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.21/0.49  thf(k2_setfam_1_type, type, k2_setfam_1: $i > $i > $i).
% 0.21/0.49  thf(t29_setfam_1, conjecture,
% 0.21/0.49    (![A:$i]: ( r1_setfam_1 @ A @ ( k2_setfam_1 @ A @ A ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]: ( r1_setfam_1 @ A @ ( k2_setfam_1 @ A @ A ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t29_setfam_1])).
% 0.21/0.49  thf('0', plain, (~ (r1_setfam_1 @ sk_A @ (k2_setfam_1 @ sk_A @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d2_setfam_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r1_setfam_1 @ A @ B ) <=>
% 0.21/0.49       ( ![C:$i]:
% 0.21/0.49         ( ~( ( r2_hidden @ C @ A ) & 
% 0.21/0.49              ( ![D:$i]: ( ~( ( r2_hidden @ D @ B ) & ( r1_tarski @ C @ D ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i]:
% 0.21/0.49         ((r1_setfam_1 @ X4 @ X5) | (r2_hidden @ (sk_C @ X5 @ X4) @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i]:
% 0.21/0.49         ((r1_setfam_1 @ X4 @ X5) | (r2_hidden @ (sk_C @ X5 @ X4) @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.21/0.49  thf(d4_setfam_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( C ) = ( k2_setfam_1 @ A @ B ) ) <=>
% 0.21/0.49       ( ![D:$i]:
% 0.21/0.49         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.49           ( ?[E:$i,F:$i]:
% 0.21/0.49             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.21/0.49               ( ( D ) = ( k2_xboole_0 @ E @ F ) ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_1, axiom,
% 0.21/0.49    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.21/0.49     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.21/0.49       ( ( ( D ) = ( k2_xboole_0 @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.21/0.49         ( r2_hidden @ E @ A ) ) ))).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X12 : $i]:
% 0.21/0.49         ((zip_tseitin_0 @ X8 @ X7 @ X9 @ X10 @ X12)
% 0.21/0.49          | ~ (r2_hidden @ X7 @ X12)
% 0.21/0.49          | ~ (r2_hidden @ X8 @ X10)
% 0.21/0.49          | ((X9) != (k2_xboole_0 @ X7 @ X8)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i, X10 : $i, X12 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X8 @ X10)
% 0.21/0.49          | ~ (r2_hidden @ X7 @ X12)
% 0.21/0.49          | (zip_tseitin_0 @ X8 @ X7 @ (k2_xboole_0 @ X7 @ X8) @ X10 @ X12))),
% 0.21/0.49      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         ((r1_setfam_1 @ X0 @ X1)
% 0.21/0.49          | (zip_tseitin_0 @ (sk_C @ X1 @ X0) @ X3 @ 
% 0.21/0.49             (k2_xboole_0 @ X3 @ (sk_C @ X1 @ X0)) @ X0 @ X2)
% 0.21/0.49          | ~ (r2_hidden @ X3 @ X2))),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '4'])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         ((r1_setfam_1 @ X0 @ X1)
% 0.21/0.49          | (zip_tseitin_0 @ (sk_C @ X3 @ X2) @ (sk_C @ X1 @ X0) @ 
% 0.21/0.49             (k2_xboole_0 @ (sk_C @ X1 @ X0) @ (sk_C @ X3 @ X2)) @ X2 @ X0)
% 0.21/0.49          | (r1_setfam_1 @ X2 @ X3))),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '5'])).
% 0.21/0.49  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.21/0.49  thf(zf_stmt_3, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( C ) = ( k2_setfam_1 @ A @ B ) ) <=>
% 0.21/0.49       ( ![D:$i]:
% 0.21/0.49         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.49           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.49         (~ (zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 @ X17)
% 0.21/0.49          | (r2_hidden @ X15 @ X18)
% 0.21/0.49          | ((X18) != (k2_setfam_1 @ X17 @ X16)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.49         ((r2_hidden @ X15 @ (k2_setfam_1 @ X17 @ X16))
% 0.21/0.49          | ~ (zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 @ X17))),
% 0.21/0.49      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         ((r1_setfam_1 @ X1 @ X2)
% 0.21/0.49          | (r1_setfam_1 @ X0 @ X3)
% 0.21/0.49          | (r2_hidden @ (k2_xboole_0 @ (sk_C @ X3 @ X0) @ (sk_C @ X2 @ X1)) @ 
% 0.21/0.49             (k2_setfam_1 @ X0 @ X1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['6', '8'])).
% 0.21/0.49  thf(t7_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.49         ((r1_setfam_1 @ X4 @ X5)
% 0.21/0.49          | ~ (r2_hidden @ X6 @ X5)
% 0.21/0.49          | ~ (r1_tarski @ (sk_C @ X5 @ X4) @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (r2_hidden @ (k2_xboole_0 @ (sk_C @ X2 @ X1) @ X0) @ X2)
% 0.21/0.49          | (r1_setfam_1 @ X1 @ X2))),
% 0.21/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((r1_setfam_1 @ X1 @ (k2_setfam_1 @ X1 @ X0))
% 0.21/0.49          | (r1_setfam_1 @ X0 @ X2)
% 0.21/0.49          | (r1_setfam_1 @ X1 @ (k2_setfam_1 @ X1 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['9', '12'])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((r1_setfam_1 @ X0 @ X2)
% 0.21/0.49          | (r1_setfam_1 @ X1 @ (k2_setfam_1 @ X1 @ X0)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.49  thf('15', plain, (![X0 : $i]: (r1_setfam_1 @ X0 @ (k2_setfam_1 @ X0 @ X0))),
% 0.21/0.49      inference('eq_fact', [status(thm)], ['14'])).
% 0.21/0.49  thf('16', plain, ($false), inference('demod', [status(thm)], ['0', '15'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
