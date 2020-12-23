%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Y4ITF2g7BY

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:30 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :   42 (  48 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :   11
%              Number of atoms          :  311 ( 406 expanded)
%              Number of equality atoms :   36 (  49 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t43_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ) )).

thf('0',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X20 @ X21 @ X22 )
      = ( k2_xboole_0 @ ( k2_tarski @ X20 @ X21 ) @ ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X8 )
      | ( X9 = X6 )
      | ( X8
       != ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('3',plain,(
    ! [X6: $i,X9: $i] :
      ( ( X9 = X6 )
      | ~ ( r2_hidden @ X9 @ ( k1_tarski @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t88_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ X5 )
        = X4 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X0 ) )
        = ( k2_tarski @ X2 @ X1 ) )
      | ( r2_hidden @ X0 @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['0','9'])).

thf(t136_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != B )
        & ( A != C )
        & ( ( k4_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ A ) )
         != ( k2_tarski @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( A != B )
          & ( A != C )
          & ( ( k4_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ A ) )
           != ( k2_tarski @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t136_enumset1])).

thf('11',plain,(
    ( k4_xboole_0 @ ( k1_enumset1 @ sk_A @ sk_B @ sk_C_2 ) @ ( k1_tarski @ sk_A ) )
 != ( k2_tarski @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t100_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ B @ C @ A ) ) )).

thf('12',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k1_enumset1 @ X19 @ X17 @ X18 )
      = ( k1_enumset1 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('13',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k1_enumset1 @ X19 @ X17 @ X18 )
      = ( k1_enumset1 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('14',plain,(
    ( k4_xboole_0 @ ( k1_enumset1 @ sk_B @ sk_C_2 @ sk_A ) @ ( k1_tarski @ sk_A ) )
 != ( k2_tarski @ sk_B @ sk_C_2 ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,
    ( ( ( k2_tarski @ sk_B @ sk_C_2 )
     != ( k2_tarski @ sk_B @ sk_C_2 ) )
    | ( r2_hidden @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,(
    r2_hidden @ sk_A @ ( k2_tarski @ sk_B @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['15'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('17',plain,(
    ! [X11: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X13 )
      | ( X15 = X14 )
      | ( X15 = X11 )
      | ( X13
       != ( k2_tarski @ X14 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('18',plain,(
    ! [X11: $i,X14: $i,X15: $i] :
      ( ( X15 = X11 )
      | ( X15 = X14 )
      | ~ ( r2_hidden @ X15 @ ( k2_tarski @ X14 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_C_2 ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    sk_A != sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['19','20','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Y4ITF2g7BY
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:39:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.55/0.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.55/0.76  % Solved by: fo/fo7.sh
% 0.55/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.76  % done 506 iterations in 0.311s
% 0.55/0.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.55/0.76  % SZS output start Refutation
% 0.55/0.76  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.55/0.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.55/0.76  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.55/0.76  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.55/0.76  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.55/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.76  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.55/0.76  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.55/0.76  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.55/0.76  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.55/0.76  thf(t43_enumset1, axiom,
% 0.55/0.76    (![A:$i,B:$i,C:$i]:
% 0.55/0.76     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.55/0.76       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ))).
% 0.55/0.76  thf('0', plain,
% 0.55/0.76      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.55/0.76         ((k1_enumset1 @ X20 @ X21 @ X22)
% 0.55/0.76           = (k2_xboole_0 @ (k2_tarski @ X20 @ X21) @ (k1_tarski @ X22)))),
% 0.55/0.76      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.55/0.76  thf(t3_xboole_0, axiom,
% 0.55/0.76    (![A:$i,B:$i]:
% 0.55/0.76     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.55/0.76            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.55/0.76       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.55/0.76            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.55/0.76  thf('1', plain,
% 0.55/0.76      (![X0 : $i, X1 : $i]:
% 0.55/0.76         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.55/0.76      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.55/0.76  thf(d1_tarski, axiom,
% 0.55/0.76    (![A:$i,B:$i]:
% 0.55/0.76     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.55/0.76       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.55/0.76  thf('2', plain,
% 0.55/0.76      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.55/0.76         (~ (r2_hidden @ X9 @ X8) | ((X9) = (X6)) | ((X8) != (k1_tarski @ X6)))),
% 0.55/0.76      inference('cnf', [status(esa)], [d1_tarski])).
% 0.55/0.76  thf('3', plain,
% 0.55/0.76      (![X6 : $i, X9 : $i]:
% 0.55/0.76         (((X9) = (X6)) | ~ (r2_hidden @ X9 @ (k1_tarski @ X6)))),
% 0.55/0.76      inference('simplify', [status(thm)], ['2'])).
% 0.55/0.76  thf('4', plain,
% 0.55/0.76      (![X0 : $i, X1 : $i]:
% 0.55/0.76         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.55/0.76          | ((sk_C @ (k1_tarski @ X0) @ X1) = (X0)))),
% 0.55/0.76      inference('sup-', [status(thm)], ['1', '3'])).
% 0.55/0.76  thf('5', plain,
% 0.55/0.76      (![X0 : $i, X1 : $i]:
% 0.55/0.76         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.55/0.76      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.55/0.76  thf('6', plain,
% 0.55/0.76      (![X0 : $i, X1 : $i]:
% 0.55/0.76         ((r2_hidden @ X0 @ X1)
% 0.55/0.76          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.55/0.76          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.55/0.76      inference('sup+', [status(thm)], ['4', '5'])).
% 0.55/0.76  thf('7', plain,
% 0.55/0.76      (![X0 : $i, X1 : $i]:
% 0.55/0.76         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0)) | (r2_hidden @ X0 @ X1))),
% 0.55/0.76      inference('simplify', [status(thm)], ['6'])).
% 0.55/0.76  thf(t88_xboole_1, axiom,
% 0.55/0.76    (![A:$i,B:$i]:
% 0.55/0.76     ( ( r1_xboole_0 @ A @ B ) =>
% 0.55/0.76       ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( A ) ) ))).
% 0.55/0.76  thf('8', plain,
% 0.55/0.76      (![X4 : $i, X5 : $i]:
% 0.55/0.76         (((k4_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ X5) = (X4))
% 0.55/0.76          | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.55/0.76      inference('cnf', [status(esa)], [t88_xboole_1])).
% 0.55/0.76  thf('9', plain,
% 0.55/0.76      (![X0 : $i, X1 : $i]:
% 0.55/0.76         ((r2_hidden @ X0 @ X1)
% 0.55/0.76          | ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)) @ 
% 0.55/0.76              (k1_tarski @ X0)) = (X1)))),
% 0.55/0.76      inference('sup-', [status(thm)], ['7', '8'])).
% 0.55/0.76  thf('10', plain,
% 0.55/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.76         (((k4_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X0))
% 0.55/0.76            = (k2_tarski @ X2 @ X1))
% 0.55/0.76          | (r2_hidden @ X0 @ (k2_tarski @ X2 @ X1)))),
% 0.55/0.76      inference('sup+', [status(thm)], ['0', '9'])).
% 0.55/0.76  thf(t136_enumset1, conjecture,
% 0.55/0.76    (![A:$i,B:$i,C:$i]:
% 0.55/0.76     ( ~( ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) & 
% 0.55/0.76          ( ( k4_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ A ) ) !=
% 0.55/0.76            ( k2_tarski @ B @ C ) ) ) ))).
% 0.55/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.76    (~( ![A:$i,B:$i,C:$i]:
% 0.55/0.76        ( ~( ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) & 
% 0.55/0.76             ( ( k4_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ A ) ) !=
% 0.55/0.76               ( k2_tarski @ B @ C ) ) ) ) )),
% 0.55/0.76    inference('cnf.neg', [status(esa)], [t136_enumset1])).
% 0.55/0.76  thf('11', plain,
% 0.55/0.76      (((k4_xboole_0 @ (k1_enumset1 @ sk_A @ sk_B @ sk_C_2) @ 
% 0.55/0.76         (k1_tarski @ sk_A)) != (k2_tarski @ sk_B @ sk_C_2))),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf(t100_enumset1, axiom,
% 0.55/0.76    (![A:$i,B:$i,C:$i]:
% 0.55/0.76     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ C @ A ) ))).
% 0.55/0.76  thf('12', plain,
% 0.55/0.76      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.55/0.76         ((k1_enumset1 @ X19 @ X17 @ X18) = (k1_enumset1 @ X17 @ X18 @ X19))),
% 0.55/0.76      inference('cnf', [status(esa)], [t100_enumset1])).
% 0.55/0.76  thf('13', plain,
% 0.55/0.76      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.55/0.76         ((k1_enumset1 @ X19 @ X17 @ X18) = (k1_enumset1 @ X17 @ X18 @ X19))),
% 0.55/0.76      inference('cnf', [status(esa)], [t100_enumset1])).
% 0.55/0.76  thf('14', plain,
% 0.55/0.76      (((k4_xboole_0 @ (k1_enumset1 @ sk_B @ sk_C_2 @ sk_A) @ 
% 0.55/0.76         (k1_tarski @ sk_A)) != (k2_tarski @ sk_B @ sk_C_2))),
% 0.55/0.76      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.55/0.76  thf('15', plain,
% 0.55/0.76      ((((k2_tarski @ sk_B @ sk_C_2) != (k2_tarski @ sk_B @ sk_C_2))
% 0.55/0.76        | (r2_hidden @ sk_A @ (k2_tarski @ sk_B @ sk_C_2)))),
% 0.55/0.76      inference('sup-', [status(thm)], ['10', '14'])).
% 0.55/0.76  thf('16', plain, ((r2_hidden @ sk_A @ (k2_tarski @ sk_B @ sk_C_2))),
% 0.55/0.76      inference('simplify', [status(thm)], ['15'])).
% 0.55/0.76  thf(d2_tarski, axiom,
% 0.55/0.76    (![A:$i,B:$i,C:$i]:
% 0.55/0.76     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.55/0.76       ( ![D:$i]:
% 0.55/0.76         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.55/0.76  thf('17', plain,
% 0.55/0.76      (![X11 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.55/0.76         (~ (r2_hidden @ X15 @ X13)
% 0.55/0.76          | ((X15) = (X14))
% 0.55/0.76          | ((X15) = (X11))
% 0.55/0.76          | ((X13) != (k2_tarski @ X14 @ X11)))),
% 0.55/0.76      inference('cnf', [status(esa)], [d2_tarski])).
% 0.55/0.76  thf('18', plain,
% 0.55/0.76      (![X11 : $i, X14 : $i, X15 : $i]:
% 0.55/0.76         (((X15) = (X11))
% 0.55/0.76          | ((X15) = (X14))
% 0.55/0.76          | ~ (r2_hidden @ X15 @ (k2_tarski @ X14 @ X11)))),
% 0.55/0.76      inference('simplify', [status(thm)], ['17'])).
% 0.55/0.76  thf('19', plain, ((((sk_A) = (sk_B)) | ((sk_A) = (sk_C_2)))),
% 0.55/0.76      inference('sup-', [status(thm)], ['16', '18'])).
% 0.55/0.76  thf('20', plain, (((sk_A) != (sk_C_2))),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('21', plain, (((sk_A) != (sk_B))),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('22', plain, ($false),
% 0.55/0.76      inference('simplify_reflect-', [status(thm)], ['19', '20', '21'])).
% 0.55/0.76  
% 0.55/0.76  % SZS output end Refutation
% 0.55/0.76  
% 0.55/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
