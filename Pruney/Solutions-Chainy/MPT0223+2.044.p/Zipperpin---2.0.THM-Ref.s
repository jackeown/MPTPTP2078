%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CbtJ9f5gPj

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:36 EST 2020

% Result     : Theorem 0.57s
% Output     : Refutation 0.57s
% Verified   : 
% Statistics : Number of formulae       :   48 (  54 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :  354 ( 417 expanded)
%              Number of equality atoms :   30 (  40 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( X22 != X21 )
      | ( r2_hidden @ X22 @ X23 )
      | ( X23
       != ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('1',plain,(
    ! [X21: $i] :
      ( r2_hidden @ X21 @ ( k1_tarski @ X21 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X3 @ ( k5_xboole_0 @ X4 @ X6 ) )
      | ( r2_hidden @ X3 @ X6 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t18_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t18_zfmisc_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k3_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('6',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( r2_hidden @ X3 @ X5 )
      | ~ ( r2_hidden @ X3 @ ( k5_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('9',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_tarski @ X26 @ X27 )
      = ( k2_xboole_0 @ ( k1_tarski @ X26 ) @ ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    | ~ ( r2_hidden @ sk_A @ ( k2_tarski @ sk_A @ sk_B_1 ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf('12',plain,(
    ! [X21: $i] :
      ( r2_hidden @ X21 @ ( k1_tarski @ X21 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('13',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    | ~ ( r2_hidden @ sk_A @ ( k2_tarski @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_enumset1 @ X29 @ X29 @ X30 )
      = ( k2_tarski @ X29 @ X30 ) ) ),
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

thf('15',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 )
      | ( r2_hidden @ X14 @ X18 )
      | ( X18
       != ( k1_enumset1 @ X17 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('16',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X14 @ ( k1_enumset1 @ X17 @ X16 @ X15 ) )
      | ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X10 != X9 )
      | ~ ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('19',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ~ ( zip_tseitin_0 @ X9 @ X11 @ X12 @ X9 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','20'])).

thf('22',plain,(
    ! [X21: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X24 @ X23 )
      | ( X24 = X21 )
      | ( X23
       != ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('23',plain,(
    ! [X21: $i,X24: $i] :
      ( ( X24 = X21 )
      | ~ ( r2_hidden @ X24 @ ( k1_tarski @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    sk_A = sk_B_1 ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CbtJ9f5gPj
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:21:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.57/0.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.57/0.76  % Solved by: fo/fo7.sh
% 0.57/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.57/0.76  % done 428 iterations in 0.306s
% 0.57/0.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.57/0.76  % SZS output start Refutation
% 0.57/0.76  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.57/0.76  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.57/0.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.57/0.76  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.57/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.57/0.76  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.57/0.76  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.57/0.76  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.57/0.76  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.57/0.76  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.57/0.76  thf(d1_tarski, axiom,
% 0.57/0.76    (![A:$i,B:$i]:
% 0.57/0.76     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.57/0.76       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.57/0.76  thf('0', plain,
% 0.57/0.76      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.57/0.76         (((X22) != (X21))
% 0.57/0.76          | (r2_hidden @ X22 @ X23)
% 0.57/0.76          | ((X23) != (k1_tarski @ X21)))),
% 0.57/0.76      inference('cnf', [status(esa)], [d1_tarski])).
% 0.57/0.76  thf('1', plain, (![X21 : $i]: (r2_hidden @ X21 @ (k1_tarski @ X21))),
% 0.57/0.76      inference('simplify', [status(thm)], ['0'])).
% 0.57/0.76  thf(t1_xboole_0, axiom,
% 0.57/0.76    (![A:$i,B:$i,C:$i]:
% 0.57/0.76     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.57/0.76       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.57/0.76  thf('2', plain,
% 0.57/0.76      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.57/0.76         ((r2_hidden @ X3 @ (k5_xboole_0 @ X4 @ X6))
% 0.57/0.76          | (r2_hidden @ X3 @ X6)
% 0.57/0.76          | ~ (r2_hidden @ X3 @ X4))),
% 0.57/0.76      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.57/0.76  thf('3', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i]:
% 0.57/0.76         ((r2_hidden @ X0 @ X1)
% 0.57/0.76          | (r2_hidden @ X0 @ (k5_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.57/0.76      inference('sup-', [status(thm)], ['1', '2'])).
% 0.57/0.76  thf(t18_zfmisc_1, conjecture,
% 0.57/0.76    (![A:$i,B:$i]:
% 0.57/0.76     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.57/0.76         ( k1_tarski @ A ) ) =>
% 0.57/0.76       ( ( A ) = ( B ) ) ))).
% 0.57/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.57/0.76    (~( ![A:$i,B:$i]:
% 0.57/0.76        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.57/0.76            ( k1_tarski @ A ) ) =>
% 0.57/0.76          ( ( A ) = ( B ) ) ) )),
% 0.57/0.76    inference('cnf.neg', [status(esa)], [t18_zfmisc_1])).
% 0.57/0.76  thf('4', plain,
% 0.57/0.76      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.57/0.76         = (k1_tarski @ sk_A))),
% 0.57/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.76  thf(t95_xboole_1, axiom,
% 0.57/0.76    (![A:$i,B:$i]:
% 0.57/0.76     ( ( k3_xboole_0 @ A @ B ) =
% 0.57/0.76       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.57/0.76  thf('5', plain,
% 0.57/0.76      (![X7 : $i, X8 : $i]:
% 0.57/0.76         ((k3_xboole_0 @ X7 @ X8)
% 0.57/0.76           = (k5_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ (k2_xboole_0 @ X7 @ X8)))),
% 0.57/0.76      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.57/0.76  thf('6', plain,
% 0.57/0.76      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.57/0.76         (~ (r2_hidden @ X3 @ X4)
% 0.57/0.76          | ~ (r2_hidden @ X3 @ X5)
% 0.57/0.76          | ~ (r2_hidden @ X3 @ (k5_xboole_0 @ X4 @ X5)))),
% 0.57/0.76      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.57/0.76  thf('7', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.76         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.57/0.76          | ~ (r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.57/0.76          | ~ (r2_hidden @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.57/0.76      inference('sup-', [status(thm)], ['5', '6'])).
% 0.57/0.76  thf('8', plain,
% 0.57/0.76      (![X0 : $i]:
% 0.57/0.76         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.57/0.76          | ~ (r2_hidden @ X0 @ 
% 0.57/0.76               (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1)))
% 0.57/0.76          | ~ (r2_hidden @ X0 @ 
% 0.57/0.76               (k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))))),
% 0.57/0.76      inference('sup-', [status(thm)], ['4', '7'])).
% 0.57/0.76  thf(t41_enumset1, axiom,
% 0.57/0.76    (![A:$i,B:$i]:
% 0.57/0.76     ( ( k2_tarski @ A @ B ) =
% 0.57/0.76       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.57/0.76  thf('9', plain,
% 0.57/0.76      (![X26 : $i, X27 : $i]:
% 0.57/0.76         ((k2_tarski @ X26 @ X27)
% 0.57/0.76           = (k2_xboole_0 @ (k1_tarski @ X26) @ (k1_tarski @ X27)))),
% 0.57/0.76      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.57/0.76  thf('10', plain,
% 0.57/0.76      (![X0 : $i]:
% 0.57/0.76         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.57/0.76          | ~ (r2_hidden @ X0 @ 
% 0.57/0.76               (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1)))
% 0.57/0.76          | ~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B_1)))),
% 0.57/0.76      inference('demod', [status(thm)], ['8', '9'])).
% 0.57/0.76  thf('11', plain,
% 0.57/0.76      (((r2_hidden @ sk_A @ (k1_tarski @ sk_B_1))
% 0.57/0.76        | ~ (r2_hidden @ sk_A @ (k2_tarski @ sk_A @ sk_B_1))
% 0.57/0.76        | ~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))),
% 0.57/0.76      inference('sup-', [status(thm)], ['3', '10'])).
% 0.57/0.76  thf('12', plain, (![X21 : $i]: (r2_hidden @ X21 @ (k1_tarski @ X21))),
% 0.57/0.76      inference('simplify', [status(thm)], ['0'])).
% 0.57/0.76  thf('13', plain,
% 0.57/0.76      (((r2_hidden @ sk_A @ (k1_tarski @ sk_B_1))
% 0.57/0.76        | ~ (r2_hidden @ sk_A @ (k2_tarski @ sk_A @ sk_B_1)))),
% 0.57/0.76      inference('demod', [status(thm)], ['11', '12'])).
% 0.57/0.76  thf(t70_enumset1, axiom,
% 0.57/0.76    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.57/0.76  thf('14', plain,
% 0.57/0.76      (![X29 : $i, X30 : $i]:
% 0.57/0.76         ((k1_enumset1 @ X29 @ X29 @ X30) = (k2_tarski @ X29 @ X30))),
% 0.57/0.76      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.57/0.76  thf(d1_enumset1, axiom,
% 0.57/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.57/0.76     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.57/0.76       ( ![E:$i]:
% 0.57/0.76         ( ( r2_hidden @ E @ D ) <=>
% 0.57/0.76           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.57/0.76  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.57/0.76  thf(zf_stmt_2, axiom,
% 0.57/0.76    (![E:$i,C:$i,B:$i,A:$i]:
% 0.57/0.76     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.57/0.76       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.57/0.76  thf(zf_stmt_3, axiom,
% 0.57/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.57/0.76     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.57/0.76       ( ![E:$i]:
% 0.57/0.76         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.57/0.76  thf('15', plain,
% 0.57/0.76      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.57/0.76         ((zip_tseitin_0 @ X14 @ X15 @ X16 @ X17)
% 0.57/0.76          | (r2_hidden @ X14 @ X18)
% 0.57/0.76          | ((X18) != (k1_enumset1 @ X17 @ X16 @ X15)))),
% 0.57/0.76      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.57/0.76  thf('16', plain,
% 0.57/0.76      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.57/0.76         ((r2_hidden @ X14 @ (k1_enumset1 @ X17 @ X16 @ X15))
% 0.57/0.76          | (zip_tseitin_0 @ X14 @ X15 @ X16 @ X17))),
% 0.57/0.76      inference('simplify', [status(thm)], ['15'])).
% 0.57/0.76  thf('17', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.76         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.57/0.76          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.57/0.76      inference('sup+', [status(thm)], ['14', '16'])).
% 0.57/0.76  thf('18', plain,
% 0.57/0.76      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.57/0.76         (((X10) != (X9)) | ~ (zip_tseitin_0 @ X10 @ X11 @ X12 @ X9))),
% 0.57/0.76      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.57/0.76  thf('19', plain,
% 0.57/0.76      (![X9 : $i, X11 : $i, X12 : $i]: ~ (zip_tseitin_0 @ X9 @ X11 @ X12 @ X9)),
% 0.57/0.76      inference('simplify', [status(thm)], ['18'])).
% 0.57/0.76  thf('20', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.57/0.76      inference('sup-', [status(thm)], ['17', '19'])).
% 0.57/0.76  thf('21', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.57/0.76      inference('demod', [status(thm)], ['13', '20'])).
% 0.57/0.76  thf('22', plain,
% 0.57/0.76      (![X21 : $i, X23 : $i, X24 : $i]:
% 0.57/0.76         (~ (r2_hidden @ X24 @ X23)
% 0.57/0.76          | ((X24) = (X21))
% 0.57/0.76          | ((X23) != (k1_tarski @ X21)))),
% 0.57/0.76      inference('cnf', [status(esa)], [d1_tarski])).
% 0.57/0.76  thf('23', plain,
% 0.57/0.76      (![X21 : $i, X24 : $i]:
% 0.57/0.76         (((X24) = (X21)) | ~ (r2_hidden @ X24 @ (k1_tarski @ X21)))),
% 0.57/0.76      inference('simplify', [status(thm)], ['22'])).
% 0.57/0.76  thf('24', plain, (((sk_A) = (sk_B_1))),
% 0.57/0.76      inference('sup-', [status(thm)], ['21', '23'])).
% 0.57/0.76  thf('25', plain, (((sk_A) != (sk_B_1))),
% 0.57/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.76  thf('26', plain, ($false),
% 0.57/0.76      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 0.57/0.76  
% 0.57/0.76  % SZS output end Refutation
% 0.57/0.76  
% 0.57/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
