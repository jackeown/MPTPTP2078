%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YfOKGH3jJT

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:15 EST 2020

% Result     : Theorem 0.71s
% Output     : Refutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :   61 (  69 expanded)
%              Number of leaves         :   25 (  31 expanded)
%              Depth                    :   12
%              Number of atoms          :  444 ( 536 expanded)
%              Number of equality atoms :   49 (  63 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 )
      | ( X11 = X12 )
      | ( X11 = X13 )
      | ( X11 = X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        & ( A != B )
        & ( A != C ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
          & ( A != B )
          & ( A != C ) ) ),
    inference('cnf.neg',[status(esa)],[t25_zfmisc_1])).

thf('1',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('5',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_xboole_0 @ X3 @ ( k2_xboole_0 @ X4 @ X5 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X3 @ X4 ) @ ( k3_xboole_0 @ X3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('9',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) ) )
    = ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k2_tarski @ sk_B @ sk_C )
    = ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_enumset1 @ X27 @ X27 @ X28 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('15',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( k2_enumset1 @ X22 @ X23 @ X24 @ X25 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X22 @ X23 @ X24 ) @ ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('17',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k2_enumset1 @ X29 @ X29 @ X30 @ X31 )
      = ( k1_enumset1 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('18',plain,
    ( ( k2_tarski @ sk_B @ sk_C )
    = ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['13','16','17'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 )
      | ( r2_hidden @ X15 @ X19 )
      | ( X19
       != ( k1_enumset1 @ X18 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('20',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ ( k1_enumset1 @ X18 @ X17 @ X16 ) )
      | ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ sk_B @ sk_C ) )
      | ( zip_tseitin_0 @ X0 @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X11 != X12 )
      | ~ ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ~ ( zip_tseitin_0 @ X12 @ X12 @ X13 @ X10 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    r2_hidden @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_enumset1 @ X27 @ X27 @ X28 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('26',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X20 @ X19 )
      | ~ ( zip_tseitin_0 @ X20 @ X16 @ X17 @ X18 )
      | ( X19
       != ( k1_enumset1 @ X18 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('27',plain,(
    ! [X16: $i,X17: $i,X18: $i,X20: $i] :
      ( ~ ( zip_tseitin_0 @ X20 @ X16 @ X17 @ X18 )
      | ~ ( r2_hidden @ X20 @ ( k1_enumset1 @ X18 @ X17 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_C @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['24','28'])).

thf('30',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_C ) ),
    inference('sup-',[status(thm)],['0','29'])).

thf('31',plain,
    ( ( sk_A = sk_C )
    | ( sk_A = sk_B ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('33',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('34',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['31','32','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YfOKGH3jJT
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:37:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.71/0.90  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.71/0.90  % Solved by: fo/fo7.sh
% 0.71/0.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.71/0.90  % done 723 iterations in 0.458s
% 0.71/0.90  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.71/0.90  % SZS output start Refutation
% 0.71/0.90  thf(sk_A_type, type, sk_A: $i).
% 0.71/0.90  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.71/0.90  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.71/0.90  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.71/0.90  thf(sk_C_type, type, sk_C: $i).
% 0.71/0.90  thf(sk_B_type, type, sk_B: $i).
% 0.71/0.90  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.71/0.90  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.71/0.90  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.71/0.90  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.71/0.90  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.71/0.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.71/0.90  thf(d1_enumset1, axiom,
% 0.71/0.90    (![A:$i,B:$i,C:$i,D:$i]:
% 0.71/0.90     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.71/0.90       ( ![E:$i]:
% 0.71/0.90         ( ( r2_hidden @ E @ D ) <=>
% 0.71/0.90           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.71/0.90  thf(zf_stmt_0, axiom,
% 0.71/0.90    (![E:$i,C:$i,B:$i,A:$i]:
% 0.71/0.90     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.71/0.90       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.71/0.90  thf('0', plain,
% 0.71/0.90      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.71/0.90         ((zip_tseitin_0 @ X11 @ X12 @ X13 @ X14)
% 0.71/0.90          | ((X11) = (X12))
% 0.71/0.90          | ((X11) = (X13))
% 0.71/0.90          | ((X11) = (X14)))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf(t25_zfmisc_1, conjecture,
% 0.71/0.90    (![A:$i,B:$i,C:$i]:
% 0.71/0.90     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.71/0.90          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 0.71/0.90  thf(zf_stmt_1, negated_conjecture,
% 0.71/0.90    (~( ![A:$i,B:$i,C:$i]:
% 0.71/0.90        ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.71/0.90             ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ) )),
% 0.71/0.90    inference('cnf.neg', [status(esa)], [t25_zfmisc_1])).
% 0.71/0.90  thf('1', plain,
% 0.71/0.90      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.71/0.90  thf(t28_xboole_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.71/0.90  thf('2', plain,
% 0.71/0.90      (![X6 : $i, X7 : $i]:
% 0.71/0.90         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.71/0.90      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.71/0.90  thf('3', plain,
% 0.71/0.90      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.71/0.90         = (k1_tarski @ sk_A))),
% 0.71/0.90      inference('sup-', [status(thm)], ['1', '2'])).
% 0.71/0.90  thf(commutativity_k3_xboole_0, axiom,
% 0.71/0.90    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.71/0.90  thf('4', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.71/0.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.71/0.90  thf(idempotence_k3_xboole_0, axiom,
% 0.71/0.90    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.71/0.90  thf('5', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.71/0.90      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.71/0.90  thf(t23_xboole_1, axiom,
% 0.71/0.90    (![A:$i,B:$i,C:$i]:
% 0.71/0.90     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.71/0.90       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.71/0.90  thf('6', plain,
% 0.71/0.90      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.71/0.90         ((k3_xboole_0 @ X3 @ (k2_xboole_0 @ X4 @ X5))
% 0.71/0.90           = (k2_xboole_0 @ (k3_xboole_0 @ X3 @ X4) @ (k3_xboole_0 @ X3 @ X5)))),
% 0.71/0.90      inference('cnf', [status(esa)], [t23_xboole_1])).
% 0.71/0.90  thf('7', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.71/0.90           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['5', '6'])).
% 0.71/0.90  thf('8', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.71/0.90           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['4', '7'])).
% 0.71/0.90  thf('9', plain,
% 0.71/0.90      (((k3_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ 
% 0.71/0.90         (k2_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_A)))
% 0.71/0.90         = (k2_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_A)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['3', '8'])).
% 0.71/0.90  thf(t7_xboole_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.71/0.90  thf('10', plain,
% 0.71/0.90      (![X8 : $i, X9 : $i]: (r1_tarski @ X8 @ (k2_xboole_0 @ X8 @ X9))),
% 0.71/0.90      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.71/0.90  thf('11', plain,
% 0.71/0.90      (![X6 : $i, X7 : $i]:
% 0.71/0.90         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.71/0.90      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.71/0.90  thf('12', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.71/0.90      inference('sup-', [status(thm)], ['10', '11'])).
% 0.71/0.90  thf('13', plain,
% 0.71/0.90      (((k2_tarski @ sk_B @ sk_C)
% 0.71/0.90         = (k2_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_A)))),
% 0.71/0.90      inference('demod', [status(thm)], ['9', '12'])).
% 0.71/0.90  thf(t70_enumset1, axiom,
% 0.71/0.90    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.71/0.90  thf('14', plain,
% 0.71/0.90      (![X27 : $i, X28 : $i]:
% 0.71/0.90         ((k1_enumset1 @ X27 @ X27 @ X28) = (k2_tarski @ X27 @ X28))),
% 0.71/0.90      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.71/0.90  thf(t46_enumset1, axiom,
% 0.71/0.90    (![A:$i,B:$i,C:$i,D:$i]:
% 0.71/0.90     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.71/0.90       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.71/0.90  thf('15', plain,
% 0.71/0.90      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.71/0.90         ((k2_enumset1 @ X22 @ X23 @ X24 @ X25)
% 0.71/0.90           = (k2_xboole_0 @ (k1_enumset1 @ X22 @ X23 @ X24) @ (k1_tarski @ X25)))),
% 0.71/0.90      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.71/0.90  thf('16', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.90         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.71/0.90           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['14', '15'])).
% 0.71/0.90  thf(t71_enumset1, axiom,
% 0.71/0.90    (![A:$i,B:$i,C:$i]:
% 0.71/0.90     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.71/0.90  thf('17', plain,
% 0.71/0.90      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.71/0.90         ((k2_enumset1 @ X29 @ X29 @ X30 @ X31)
% 0.71/0.90           = (k1_enumset1 @ X29 @ X30 @ X31))),
% 0.71/0.90      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.71/0.90  thf('18', plain,
% 0.71/0.90      (((k2_tarski @ sk_B @ sk_C) = (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 0.71/0.90      inference('demod', [status(thm)], ['13', '16', '17'])).
% 0.71/0.90  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.71/0.90  thf(zf_stmt_3, axiom,
% 0.71/0.90    (![A:$i,B:$i,C:$i,D:$i]:
% 0.71/0.90     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.71/0.90       ( ![E:$i]:
% 0.71/0.90         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.71/0.90  thf('19', plain,
% 0.71/0.90      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.71/0.90         ((zip_tseitin_0 @ X15 @ X16 @ X17 @ X18)
% 0.71/0.90          | (r2_hidden @ X15 @ X19)
% 0.71/0.90          | ((X19) != (k1_enumset1 @ X18 @ X17 @ X16)))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.71/0.90  thf('20', plain,
% 0.71/0.90      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.71/0.90         ((r2_hidden @ X15 @ (k1_enumset1 @ X18 @ X17 @ X16))
% 0.71/0.90          | (zip_tseitin_0 @ X15 @ X16 @ X17 @ X18))),
% 0.71/0.90      inference('simplify', [status(thm)], ['19'])).
% 0.71/0.90  thf('21', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         ((r2_hidden @ X0 @ (k2_tarski @ sk_B @ sk_C))
% 0.71/0.90          | (zip_tseitin_0 @ X0 @ sk_A @ sk_C @ sk_B))),
% 0.71/0.90      inference('sup+', [status(thm)], ['18', '20'])).
% 0.71/0.91  thf('22', plain,
% 0.71/0.91      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.71/0.91         (((X11) != (X12)) | ~ (zip_tseitin_0 @ X11 @ X12 @ X13 @ X10))),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('23', plain,
% 0.71/0.91      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.71/0.91         ~ (zip_tseitin_0 @ X12 @ X12 @ X13 @ X10)),
% 0.71/0.91      inference('simplify', [status(thm)], ['22'])).
% 0.71/0.91  thf('24', plain, ((r2_hidden @ sk_A @ (k2_tarski @ sk_B @ sk_C))),
% 0.71/0.91      inference('sup-', [status(thm)], ['21', '23'])).
% 0.71/0.91  thf('25', plain,
% 0.71/0.91      (![X27 : $i, X28 : $i]:
% 0.71/0.91         ((k1_enumset1 @ X27 @ X27 @ X28) = (k2_tarski @ X27 @ X28))),
% 0.71/0.91      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.71/0.91  thf('26', plain,
% 0.71/0.91      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.71/0.91         (~ (r2_hidden @ X20 @ X19)
% 0.71/0.91          | ~ (zip_tseitin_0 @ X20 @ X16 @ X17 @ X18)
% 0.71/0.91          | ((X19) != (k1_enumset1 @ X18 @ X17 @ X16)))),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.71/0.91  thf('27', plain,
% 0.71/0.91      (![X16 : $i, X17 : $i, X18 : $i, X20 : $i]:
% 0.71/0.91         (~ (zip_tseitin_0 @ X20 @ X16 @ X17 @ X18)
% 0.71/0.91          | ~ (r2_hidden @ X20 @ (k1_enumset1 @ X18 @ X17 @ X16)))),
% 0.71/0.91      inference('simplify', [status(thm)], ['26'])).
% 0.71/0.91  thf('28', plain,
% 0.71/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.91         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.71/0.91          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.71/0.91      inference('sup-', [status(thm)], ['25', '27'])).
% 0.71/0.91  thf('29', plain, (~ (zip_tseitin_0 @ sk_A @ sk_C @ sk_B @ sk_B)),
% 0.71/0.91      inference('sup-', [status(thm)], ['24', '28'])).
% 0.71/0.91  thf('30', plain,
% 0.71/0.91      ((((sk_A) = (sk_B)) | ((sk_A) = (sk_B)) | ((sk_A) = (sk_C)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['0', '29'])).
% 0.71/0.91  thf('31', plain, ((((sk_A) = (sk_C)) | ((sk_A) = (sk_B)))),
% 0.71/0.91      inference('simplify', [status(thm)], ['30'])).
% 0.71/0.91  thf('32', plain, (((sk_A) != (sk_B))),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.71/0.91  thf('33', plain, (((sk_A) != (sk_C))),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.71/0.91  thf('34', plain, ($false),
% 0.71/0.91      inference('simplify_reflect-', [status(thm)], ['31', '32', '33'])).
% 0.71/0.91  
% 0.71/0.91  % SZS output end Refutation
% 0.71/0.91  
% 0.71/0.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
