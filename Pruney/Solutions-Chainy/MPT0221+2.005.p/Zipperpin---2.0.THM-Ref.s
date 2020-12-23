%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nrffmQ0aF4

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:27 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   45 (  48 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :  249 ( 268 expanded)
%              Number of equality atoms :   24 (  26 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(t16_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        & ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          & ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t16_zfmisc_1])).

thf('0',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    sk_A = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('3',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X9 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('4',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('5',plain,(
    ! [X22: $i] :
      ( ( k2_tarski @ X22 @ X22 )
      = ( k1_tarski @ X22 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_enumset1 @ X23 @ X23 @ X24 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
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

thf('7',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 )
      | ( r2_hidden @ X15 @ X19 )
      | ( X19
       != ( k1_enumset1 @ X18 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('8',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ ( k1_enumset1 @ X18 @ X17 @ X16 ) )
      | ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X11 != X10 )
      | ~ ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('11',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ~ ( zip_tseitin_0 @ X10 @ X12 @ X13 @ X10 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','12'])).

thf('14',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['4','13'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('15',plain,(
    ! [X7: $i] :
      ( r1_xboole_0 @ X7 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('18',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X7: $i] :
      ( r1_xboole_0 @ X7 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('21',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    $false ),
    inference('sup-',[status(thm)],['14','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nrffmQ0aF4
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:24:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 43 iterations in 0.025s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.49  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.22/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.22/0.49  thf(t16_zfmisc_1, conjecture,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) & 
% 0.22/0.49          ( ( A ) = ( B ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i,B:$i]:
% 0.22/0.49        ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) & 
% 0.22/0.49             ( ( A ) = ( B ) ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t16_zfmisc_1])).
% 0.22/0.49  thf('0', plain, ((r1_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('1', plain, (((sk_A) = (sk_B))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('2', plain, ((r1_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['0', '1'])).
% 0.22/0.49  thf(t66_xboole_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.22/0.49       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      (![X9 : $i]: (((X9) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X9 @ X9))),
% 0.22/0.49      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.22/0.49  thf('4', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.49  thf(t69_enumset1, axiom,
% 0.22/0.49    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.49  thf('5', plain, (![X22 : $i]: ((k2_tarski @ X22 @ X22) = (k1_tarski @ X22))),
% 0.22/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.49  thf(t70_enumset1, axiom,
% 0.22/0.49    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      (![X23 : $i, X24 : $i]:
% 0.22/0.49         ((k1_enumset1 @ X23 @ X23 @ X24) = (k2_tarski @ X23 @ X24))),
% 0.22/0.49      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.49  thf(d1_enumset1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.49     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.22/0.49       ( ![E:$i]:
% 0.22/0.49         ( ( r2_hidden @ E @ D ) <=>
% 0.22/0.49           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.22/0.49  thf(zf_stmt_2, axiom,
% 0.22/0.49    (![E:$i,C:$i,B:$i,A:$i]:
% 0.22/0.49     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.22/0.49       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_3, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.49     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.22/0.49       ( ![E:$i]:
% 0.22/0.49         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.49         ((zip_tseitin_0 @ X15 @ X16 @ X17 @ X18)
% 0.22/0.49          | (r2_hidden @ X15 @ X19)
% 0.22/0.49          | ((X19) != (k1_enumset1 @ X18 @ X17 @ X16)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.49         ((r2_hidden @ X15 @ (k1_enumset1 @ X18 @ X17 @ X16))
% 0.22/0.49          | (zip_tseitin_0 @ X15 @ X16 @ X17 @ X18))),
% 0.22/0.49      inference('simplify', [status(thm)], ['7'])).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.22/0.49          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.22/0.49      inference('sup+', [status(thm)], ['6', '8'])).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.49         (((X11) != (X10)) | ~ (zip_tseitin_0 @ X11 @ X12 @ X13 @ X10))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.22/0.49         ~ (zip_tseitin_0 @ X10 @ X12 @ X13 @ X10)),
% 0.22/0.49      inference('simplify', [status(thm)], ['10'])).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.22/0.49      inference('sup-', [status(thm)], ['9', '11'])).
% 0.22/0.49  thf('13', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['5', '12'])).
% 0.22/0.49  thf('14', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.22/0.49      inference('sup+', [status(thm)], ['4', '13'])).
% 0.22/0.49  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.22/0.49  thf('15', plain, (![X7 : $i]: (r1_xboole_0 @ X7 @ k1_xboole_0)),
% 0.22/0.49      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.22/0.49  thf(d7_xboole_0, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.22/0.49       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.49  thf(t4_xboole_0, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.49            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.49       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.22/0.49            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.22/0.49          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.22/0.49      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.49  thf('20', plain, (![X7 : $i]: (r1_xboole_0 @ X7 @ k1_xboole_0)),
% 0.22/0.49      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.22/0.49  thf('21', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.22/0.49      inference('demod', [status(thm)], ['19', '20'])).
% 0.22/0.49  thf('22', plain, ($false), inference('sup-', [status(thm)], ['14', '21'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
