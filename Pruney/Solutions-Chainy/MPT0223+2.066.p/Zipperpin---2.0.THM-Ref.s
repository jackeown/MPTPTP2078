%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gOilLmXL4b

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:39 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   61 (  67 expanded)
%              Number of leaves         :   25 (  30 expanded)
%              Depth                    :   12
%              Number of atoms          :  405 ( 472 expanded)
%              Number of equality atoms :   49 (  59 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf(t18_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t18_zfmisc_1])).

thf('1',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('3',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) )
      = X2 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','8'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('11',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('13',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('14',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_tarski @ X24 @ X25 )
      = ( k2_xboole_0 @ ( k1_tarski @ X24 ) @ ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('15',plain,
    ( ( k2_tarski @ sk_B @ sk_A )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_enumset1 @ X27 @ X27 @ X28 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 )
      | ( r2_hidden @ X14 @ X18 )
      | ( X18
       != ( k1_enumset1 @ X17 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('18',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X14 @ ( k1_enumset1 @ X17 @ X16 @ X15 ) )
      | ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X10 != X11 )
      | ~ ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ~ ( zip_tseitin_0 @ X11 @ X11 @ X12 @ X9 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup+',[status(thm)],['15','22'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('24',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('25',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_enumset1 @ X27 @ X27 @ X28 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('26',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X18 )
      | ~ ( zip_tseitin_0 @ X19 @ X15 @ X16 @ X17 )
      | ( X18
       != ( k1_enumset1 @ X17 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('27',plain,(
    ! [X15: $i,X16: $i,X17: $i,X19: $i] :
      ( ~ ( zip_tseitin_0 @ X19 @ X15 @ X16 @ X17 )
      | ~ ( r2_hidden @ X19 @ ( k1_enumset1 @ X17 @ X16 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','28'])).

thf('30',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['23','29'])).

thf('31',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['0','30'])).

thf('32',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('34',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['32','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gOilLmXL4b
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:58:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.57  % Solved by: fo/fo7.sh
% 0.38/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.57  % done 288 iterations in 0.111s
% 0.38/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.57  % SZS output start Refutation
% 0.38/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.57  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.38/0.57  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.38/0.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.38/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.57  thf(d1_enumset1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.57     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.38/0.57       ( ![E:$i]:
% 0.38/0.57         ( ( r2_hidden @ E @ D ) <=>
% 0.38/0.57           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.38/0.57  thf(zf_stmt_0, axiom,
% 0.38/0.57    (![E:$i,C:$i,B:$i,A:$i]:
% 0.38/0.57     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.38/0.57       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.38/0.57  thf('0', plain,
% 0.38/0.57      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.38/0.57         ((zip_tseitin_0 @ X10 @ X11 @ X12 @ X13)
% 0.38/0.57          | ((X10) = (X11))
% 0.38/0.57          | ((X10) = (X12))
% 0.38/0.57          | ((X10) = (X13)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(t18_zfmisc_1, conjecture,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.38/0.57         ( k1_tarski @ A ) ) =>
% 0.38/0.57       ( ( A ) = ( B ) ) ))).
% 0.38/0.57  thf(zf_stmt_1, negated_conjecture,
% 0.38/0.57    (~( ![A:$i,B:$i]:
% 0.38/0.57        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.38/0.57            ( k1_tarski @ A ) ) =>
% 0.38/0.57          ( ( A ) = ( B ) ) ) )),
% 0.38/0.57    inference('cnf.neg', [status(esa)], [t18_zfmisc_1])).
% 0.38/0.57  thf('1', plain,
% 0.38/0.57      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.38/0.57         = (k1_tarski @ sk_A))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.57  thf(t100_xboole_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.38/0.57  thf('2', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         ((k4_xboole_0 @ X0 @ X1)
% 0.38/0.57           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.38/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.57  thf('3', plain,
% 0.38/0.57      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.38/0.57         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.38/0.57      inference('sup+', [status(thm)], ['1', '2'])).
% 0.38/0.57  thf(t21_xboole_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.38/0.57  thf('4', plain,
% 0.38/0.57      (![X2 : $i, X3 : $i]:
% 0.38/0.57         ((k3_xboole_0 @ X2 @ (k2_xboole_0 @ X2 @ X3)) = (X2))),
% 0.38/0.57      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.38/0.57  thf('5', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         ((k4_xboole_0 @ X0 @ X1)
% 0.38/0.57           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.38/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.57  thf('6', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.38/0.57           = (k5_xboole_0 @ X0 @ X0))),
% 0.38/0.57      inference('sup+', [status(thm)], ['4', '5'])).
% 0.38/0.57  thf(t46_xboole_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.38/0.57  thf('7', plain,
% 0.38/0.57      (![X4 : $i, X5 : $i]:
% 0.38/0.57         ((k4_xboole_0 @ X4 @ (k2_xboole_0 @ X4 @ X5)) = (k1_xboole_0))),
% 0.38/0.57      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.38/0.57  thf('8', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.38/0.57      inference('sup+', [status(thm)], ['6', '7'])).
% 0.38/0.57  thf('9', plain,
% 0.38/0.57      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.38/0.57      inference('demod', [status(thm)], ['3', '8'])).
% 0.38/0.57  thf(t98_xboole_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.38/0.57  thf('10', plain,
% 0.38/0.57      (![X7 : $i, X8 : $i]:
% 0.38/0.57         ((k2_xboole_0 @ X7 @ X8)
% 0.38/0.57           = (k5_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7)))),
% 0.38/0.57      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.38/0.57  thf('11', plain,
% 0.38/0.57      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.38/0.57         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0))),
% 0.38/0.57      inference('sup+', [status(thm)], ['9', '10'])).
% 0.38/0.57  thf(t5_boole, axiom,
% 0.38/0.57    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.38/0.57  thf('12', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.38/0.57      inference('cnf', [status(esa)], [t5_boole])).
% 0.38/0.57  thf('13', plain,
% 0.38/0.57      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.38/0.57         = (k1_tarski @ sk_B))),
% 0.38/0.57      inference('demod', [status(thm)], ['11', '12'])).
% 0.38/0.57  thf(t41_enumset1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( k2_tarski @ A @ B ) =
% 0.38/0.57       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.38/0.57  thf('14', plain,
% 0.38/0.57      (![X24 : $i, X25 : $i]:
% 0.38/0.57         ((k2_tarski @ X24 @ X25)
% 0.38/0.57           = (k2_xboole_0 @ (k1_tarski @ X24) @ (k1_tarski @ X25)))),
% 0.38/0.57      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.38/0.57  thf('15', plain, (((k2_tarski @ sk_B @ sk_A) = (k1_tarski @ sk_B))),
% 0.38/0.57      inference('demod', [status(thm)], ['13', '14'])).
% 0.38/0.57  thf(t70_enumset1, axiom,
% 0.38/0.57    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.38/0.57  thf('16', plain,
% 0.38/0.57      (![X27 : $i, X28 : $i]:
% 0.38/0.57         ((k1_enumset1 @ X27 @ X27 @ X28) = (k2_tarski @ X27 @ X28))),
% 0.38/0.57      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.38/0.57  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.38/0.57  thf(zf_stmt_3, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.57     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.38/0.57       ( ![E:$i]:
% 0.38/0.57         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.38/0.57  thf('17', plain,
% 0.38/0.57      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.38/0.57         ((zip_tseitin_0 @ X14 @ X15 @ X16 @ X17)
% 0.38/0.57          | (r2_hidden @ X14 @ X18)
% 0.38/0.57          | ((X18) != (k1_enumset1 @ X17 @ X16 @ X15)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.38/0.57  thf('18', plain,
% 0.38/0.57      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.38/0.57         ((r2_hidden @ X14 @ (k1_enumset1 @ X17 @ X16 @ X15))
% 0.38/0.57          | (zip_tseitin_0 @ X14 @ X15 @ X16 @ X17))),
% 0.38/0.57      inference('simplify', [status(thm)], ['17'])).
% 0.38/0.57  thf('19', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.57         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.38/0.57          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.38/0.57      inference('sup+', [status(thm)], ['16', '18'])).
% 0.38/0.57  thf('20', plain,
% 0.38/0.57      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.38/0.57         (((X10) != (X11)) | ~ (zip_tseitin_0 @ X10 @ X11 @ X12 @ X9))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('21', plain,
% 0.38/0.57      (![X9 : $i, X11 : $i, X12 : $i]: ~ (zip_tseitin_0 @ X11 @ X11 @ X12 @ X9)),
% 0.38/0.57      inference('simplify', [status(thm)], ['20'])).
% 0.38/0.57  thf('22', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.38/0.57      inference('sup-', [status(thm)], ['19', '21'])).
% 0.38/0.57  thf('23', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.38/0.57      inference('sup+', [status(thm)], ['15', '22'])).
% 0.38/0.57  thf(t69_enumset1, axiom,
% 0.38/0.57    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.38/0.57  thf('24', plain,
% 0.38/0.57      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 0.38/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.38/0.57  thf('25', plain,
% 0.38/0.57      (![X27 : $i, X28 : $i]:
% 0.38/0.57         ((k1_enumset1 @ X27 @ X27 @ X28) = (k2_tarski @ X27 @ X28))),
% 0.38/0.57      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.38/0.57  thf('26', plain,
% 0.38/0.57      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.38/0.57         (~ (r2_hidden @ X19 @ X18)
% 0.38/0.57          | ~ (zip_tseitin_0 @ X19 @ X15 @ X16 @ X17)
% 0.38/0.57          | ((X18) != (k1_enumset1 @ X17 @ X16 @ X15)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.38/0.57  thf('27', plain,
% 0.38/0.57      (![X15 : $i, X16 : $i, X17 : $i, X19 : $i]:
% 0.38/0.57         (~ (zip_tseitin_0 @ X19 @ X15 @ X16 @ X17)
% 0.38/0.57          | ~ (r2_hidden @ X19 @ (k1_enumset1 @ X17 @ X16 @ X15)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['26'])).
% 0.38/0.57  thf('28', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.57         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.38/0.57          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.38/0.57      inference('sup-', [status(thm)], ['25', '27'])).
% 0.38/0.57  thf('29', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.38/0.57          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['24', '28'])).
% 0.38/0.57  thf('30', plain, (~ (zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B)),
% 0.38/0.57      inference('sup-', [status(thm)], ['23', '29'])).
% 0.38/0.57  thf('31', plain,
% 0.38/0.57      ((((sk_A) = (sk_B)) | ((sk_A) = (sk_B)) | ((sk_A) = (sk_B)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['0', '30'])).
% 0.38/0.57  thf('32', plain, (((sk_A) = (sk_B))),
% 0.38/0.57      inference('simplify', [status(thm)], ['31'])).
% 0.38/0.57  thf('33', plain, (((sk_A) != (sk_B))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.57  thf('34', plain, ($false),
% 0.38/0.57      inference('simplify_reflect-', [status(thm)], ['32', '33'])).
% 0.38/0.57  
% 0.38/0.57  % SZS output end Refutation
% 0.38/0.57  
% 0.38/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
