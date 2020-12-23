%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OzvRh8x0A7

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:39 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   57 (  66 expanded)
%              Number of leaves         :   22 (  29 expanded)
%              Depth                    :   14
%              Number of atoms          :  393 ( 500 expanded)
%              Number of equality atoms :   39 (  54 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X13 )
      | ( X10 = X11 )
      | ( X10 = X12 )
      | ( X10 = X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
        & ( A != C )
        & ( A != D ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
          & ( A != C )
          & ( A != D ) ) ),
    inference('cnf.neg',[status(esa)],[t28_zfmisc_1])).

thf('1',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('3',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) )
    = ( k2_tarski @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_enumset1 @ X25 @ X25 @ X26 )
      = ( k2_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k1_enumset1 @ X21 @ X22 @ X23 )
      = ( k2_xboole_0 @ ( k1_tarski @ X21 ) @ ( k2_tarski @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k1_tarski @ X2 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ X2 @ ( k2_xboole_0 @ X4 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k1_tarski @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','11'])).

thf('13',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['3','12'])).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('15',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D ) )
    = ( k2_tarski @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k1_enumset1 @ X21 @ X22 @ X23 )
      = ( k2_xboole_0 @ ( k1_tarski @ X21 ) @ ( k2_tarski @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('17',plain,
    ( ( k1_enumset1 @ sk_A @ sk_C @ sk_D )
    = ( k2_tarski @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 )
      | ( r2_hidden @ X14 @ X18 )
      | ( X18
       != ( k1_enumset1 @ X17 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('19',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X14 @ ( k1_enumset1 @ X17 @ X16 @ X15 ) )
      | ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ sk_C @ sk_D ) )
      | ( zip_tseitin_0 @ X0 @ sk_D @ sk_C @ sk_A ) ) ),
    inference('sup+',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X10 != X9 )
      | ~ ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ~ ( zip_tseitin_0 @ X9 @ X11 @ X12 @ X9 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    r2_hidden @ sk_A @ ( k2_tarski @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_enumset1 @ X25 @ X25 @ X26 )
      = ( k2_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('25',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X18 )
      | ~ ( zip_tseitin_0 @ X19 @ X15 @ X16 @ X17 )
      | ( X18
       != ( k1_enumset1 @ X17 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('26',plain,(
    ! [X15: $i,X16: $i,X17: $i,X19: $i] :
      ( ~ ( zip_tseitin_0 @ X19 @ X15 @ X16 @ X17 )
      | ~ ( r2_hidden @ X19 @ ( k1_enumset1 @ X17 @ X16 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_D @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['23','27'])).

thf('29',plain,
    ( ( sk_A = sk_C )
    | ( sk_A = sk_C )
    | ( sk_A = sk_D ) ),
    inference('sup-',[status(thm)],['0','28'])).

thf('30',plain,
    ( ( sk_A = sk_D )
    | ( sk_A = sk_C ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('32',plain,(
    sk_A != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('33',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['30','31','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OzvRh8x0A7
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:31:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.52/0.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.52/0.72  % Solved by: fo/fo7.sh
% 0.52/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.72  % done 610 iterations in 0.263s
% 0.52/0.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.52/0.72  % SZS output start Refutation
% 0.52/0.72  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.52/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.72  thf(sk_C_type, type, sk_C: $i).
% 0.52/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.72  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.52/0.72  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.52/0.72  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.52/0.72  thf(sk_D_type, type, sk_D: $i).
% 0.52/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.72  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.52/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.72  thf(d1_enumset1, axiom,
% 0.52/0.72    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.72     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.52/0.72       ( ![E:$i]:
% 0.52/0.72         ( ( r2_hidden @ E @ D ) <=>
% 0.52/0.72           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.52/0.72  thf(zf_stmt_0, axiom,
% 0.52/0.72    (![E:$i,C:$i,B:$i,A:$i]:
% 0.52/0.72     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.52/0.72       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.52/0.72  thf('0', plain,
% 0.52/0.72      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.52/0.72         ((zip_tseitin_0 @ X10 @ X11 @ X12 @ X13)
% 0.52/0.72          | ((X10) = (X11))
% 0.52/0.72          | ((X10) = (X12))
% 0.52/0.72          | ((X10) = (X13)))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf(t28_zfmisc_1, conjecture,
% 0.52/0.72    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.72     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.52/0.72          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 0.52/0.72  thf(zf_stmt_1, negated_conjecture,
% 0.52/0.72    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.72        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.52/0.72             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 0.52/0.72    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 0.52/0.72  thf('1', plain,
% 0.52/0.72      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.52/0.72  thf(t12_xboole_1, axiom,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.52/0.72  thf('2', plain,
% 0.52/0.72      (![X5 : $i, X6 : $i]:
% 0.52/0.72         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 0.52/0.72      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.52/0.72  thf('3', plain,
% 0.52/0.72      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D))
% 0.52/0.72         = (k2_tarski @ sk_C @ sk_D))),
% 0.52/0.72      inference('sup-', [status(thm)], ['1', '2'])).
% 0.52/0.72  thf(commutativity_k2_xboole_0, axiom,
% 0.52/0.72    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.52/0.72  thf('4', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.52/0.72      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.52/0.72  thf(t70_enumset1, axiom,
% 0.52/0.72    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.52/0.72  thf('5', plain,
% 0.52/0.72      (![X25 : $i, X26 : $i]:
% 0.52/0.72         ((k1_enumset1 @ X25 @ X25 @ X26) = (k2_tarski @ X25 @ X26))),
% 0.52/0.72      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.52/0.72  thf(t42_enumset1, axiom,
% 0.52/0.72    (![A:$i,B:$i,C:$i]:
% 0.52/0.72     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.52/0.72       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.52/0.72  thf('6', plain,
% 0.52/0.72      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.52/0.72         ((k1_enumset1 @ X21 @ X22 @ X23)
% 0.52/0.72           = (k2_xboole_0 @ (k1_tarski @ X21) @ (k2_tarski @ X22 @ X23)))),
% 0.52/0.72      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.52/0.72  thf(t7_xboole_1, axiom,
% 0.52/0.72    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.52/0.72  thf('7', plain,
% 0.52/0.72      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 0.52/0.72      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.52/0.72  thf('8', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.72         (r1_tarski @ (k1_tarski @ X2) @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.52/0.72      inference('sup+', [status(thm)], ['6', '7'])).
% 0.52/0.72  thf('9', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         (r1_tarski @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.52/0.72      inference('sup+', [status(thm)], ['5', '8'])).
% 0.52/0.72  thf(t10_xboole_1, axiom,
% 0.52/0.72    (![A:$i,B:$i,C:$i]:
% 0.52/0.72     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.52/0.72  thf('10', plain,
% 0.52/0.72      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.52/0.72         (~ (r1_tarski @ X2 @ X3) | (r1_tarski @ X2 @ (k2_xboole_0 @ X4 @ X3)))),
% 0.52/0.72      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.52/0.72  thf('11', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.72         (r1_tarski @ (k1_tarski @ X1) @ 
% 0.52/0.72          (k2_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)))),
% 0.52/0.72      inference('sup-', [status(thm)], ['9', '10'])).
% 0.52/0.72  thf('12', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.72         (r1_tarski @ (k1_tarski @ X2) @ 
% 0.52/0.72          (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0))),
% 0.52/0.72      inference('sup+', [status(thm)], ['4', '11'])).
% 0.52/0.72  thf('13', plain,
% 0.52/0.72      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D))),
% 0.52/0.72      inference('sup+', [status(thm)], ['3', '12'])).
% 0.52/0.72  thf('14', plain,
% 0.52/0.72      (![X5 : $i, X6 : $i]:
% 0.52/0.72         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 0.52/0.72      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.52/0.72  thf('15', plain,
% 0.52/0.72      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D))
% 0.52/0.72         = (k2_tarski @ sk_C @ sk_D))),
% 0.52/0.72      inference('sup-', [status(thm)], ['13', '14'])).
% 0.52/0.72  thf('16', plain,
% 0.52/0.72      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.52/0.72         ((k1_enumset1 @ X21 @ X22 @ X23)
% 0.52/0.72           = (k2_xboole_0 @ (k1_tarski @ X21) @ (k2_tarski @ X22 @ X23)))),
% 0.52/0.72      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.52/0.72  thf('17', plain,
% 0.52/0.72      (((k1_enumset1 @ sk_A @ sk_C @ sk_D) = (k2_tarski @ sk_C @ sk_D))),
% 0.52/0.72      inference('demod', [status(thm)], ['15', '16'])).
% 0.52/0.72  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.52/0.72  thf(zf_stmt_3, axiom,
% 0.52/0.72    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.72     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.52/0.72       ( ![E:$i]:
% 0.52/0.72         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.52/0.72  thf('18', plain,
% 0.52/0.72      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.52/0.72         ((zip_tseitin_0 @ X14 @ X15 @ X16 @ X17)
% 0.52/0.72          | (r2_hidden @ X14 @ X18)
% 0.52/0.72          | ((X18) != (k1_enumset1 @ X17 @ X16 @ X15)))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.52/0.72  thf('19', plain,
% 0.52/0.72      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.52/0.72         ((r2_hidden @ X14 @ (k1_enumset1 @ X17 @ X16 @ X15))
% 0.52/0.72          | (zip_tseitin_0 @ X14 @ X15 @ X16 @ X17))),
% 0.52/0.72      inference('simplify', [status(thm)], ['18'])).
% 0.52/0.72  thf('20', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         ((r2_hidden @ X0 @ (k2_tarski @ sk_C @ sk_D))
% 0.52/0.72          | (zip_tseitin_0 @ X0 @ sk_D @ sk_C @ sk_A))),
% 0.52/0.72      inference('sup+', [status(thm)], ['17', '19'])).
% 0.52/0.72  thf('21', plain,
% 0.52/0.72      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.52/0.72         (((X10) != (X9)) | ~ (zip_tseitin_0 @ X10 @ X11 @ X12 @ X9))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('22', plain,
% 0.52/0.72      (![X9 : $i, X11 : $i, X12 : $i]: ~ (zip_tseitin_0 @ X9 @ X11 @ X12 @ X9)),
% 0.52/0.72      inference('simplify', [status(thm)], ['21'])).
% 0.52/0.72  thf('23', plain, ((r2_hidden @ sk_A @ (k2_tarski @ sk_C @ sk_D))),
% 0.52/0.72      inference('sup-', [status(thm)], ['20', '22'])).
% 0.52/0.72  thf('24', plain,
% 0.52/0.72      (![X25 : $i, X26 : $i]:
% 0.52/0.72         ((k1_enumset1 @ X25 @ X25 @ X26) = (k2_tarski @ X25 @ X26))),
% 0.52/0.72      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.52/0.72  thf('25', plain,
% 0.52/0.72      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.52/0.72         (~ (r2_hidden @ X19 @ X18)
% 0.52/0.72          | ~ (zip_tseitin_0 @ X19 @ X15 @ X16 @ X17)
% 0.52/0.72          | ((X18) != (k1_enumset1 @ X17 @ X16 @ X15)))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.52/0.72  thf('26', plain,
% 0.52/0.72      (![X15 : $i, X16 : $i, X17 : $i, X19 : $i]:
% 0.52/0.72         (~ (zip_tseitin_0 @ X19 @ X15 @ X16 @ X17)
% 0.52/0.72          | ~ (r2_hidden @ X19 @ (k1_enumset1 @ X17 @ X16 @ X15)))),
% 0.52/0.72      inference('simplify', [status(thm)], ['25'])).
% 0.52/0.72  thf('27', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.72         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.52/0.72          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.52/0.72      inference('sup-', [status(thm)], ['24', '26'])).
% 0.52/0.72  thf('28', plain, (~ (zip_tseitin_0 @ sk_A @ sk_D @ sk_C @ sk_C)),
% 0.52/0.72      inference('sup-', [status(thm)], ['23', '27'])).
% 0.52/0.72  thf('29', plain,
% 0.52/0.72      ((((sk_A) = (sk_C)) | ((sk_A) = (sk_C)) | ((sk_A) = (sk_D)))),
% 0.52/0.72      inference('sup-', [status(thm)], ['0', '28'])).
% 0.52/0.72  thf('30', plain, ((((sk_A) = (sk_D)) | ((sk_A) = (sk_C)))),
% 0.52/0.72      inference('simplify', [status(thm)], ['29'])).
% 0.52/0.72  thf('31', plain, (((sk_A) != (sk_C))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.52/0.72  thf('32', plain, (((sk_A) != (sk_D))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.52/0.72  thf('33', plain, ($false),
% 0.52/0.72      inference('simplify_reflect-', [status(thm)], ['30', '31', '32'])).
% 0.52/0.72  
% 0.52/0.72  % SZS output end Refutation
% 0.52/0.72  
% 0.52/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
