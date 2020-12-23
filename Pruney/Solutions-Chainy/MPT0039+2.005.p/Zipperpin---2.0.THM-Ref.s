%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iOidIdYi5w

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:58 EST 2020

% Result     : Theorem 7.31s
% Output     : Refutation 7.31s
% Verified   : 
% Statistics : Number of formulae       :   36 (  79 expanded)
%              Number of leaves         :    8 (  24 expanded)
%              Depth                    :   13
%              Number of atoms          :  273 ( 730 expanded)
%              Number of equality atoms :   20 (  67 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t32_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = ( k4_xboole_0 @ B @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ A @ B )
          = ( k4_xboole_0 @ B @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t32_xboole_1])).

thf('0',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X7 = X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X7 ) @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('7',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('10',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ sk_A @ X0 ) @ sk_B )
      | ( X0 = sk_A )
      | ( r2_hidden @ ( sk_C @ sk_A @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,
    ( ( sk_B = sk_A )
    | ( r2_hidden @ ( sk_C @ sk_A @ sk_B ) @ sk_B ) ),
    inference(eq_fact,[status(thm)],['12'])).

thf('14',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    r2_hidden @ ( sk_C @ sk_A @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r2_hidden @ ( sk_C @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_C @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['0','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['8','10'])).

thf('20',plain,(
    r2_hidden @ ( sk_C @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X7 = X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X7 ) @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('22',plain,
    ( ~ ( r2_hidden @ ( sk_C @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r2_hidden @ ( sk_C @ sk_A @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

thf('24',plain,(
    sk_B = sk_A ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iOidIdYi5w
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:37:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 7.31/7.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 7.31/7.52  % Solved by: fo/fo7.sh
% 7.31/7.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.31/7.52  % done 8420 iterations in 7.065s
% 7.31/7.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 7.31/7.52  % SZS output start Refutation
% 7.31/7.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 7.31/7.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 7.31/7.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 7.31/7.52  thf(sk_A_type, type, sk_A: $i).
% 7.31/7.52  thf(sk_B_type, type, sk_B: $i).
% 7.31/7.52  thf(t32_xboole_1, conjecture,
% 7.31/7.52    (![A:$i,B:$i]:
% 7.31/7.52     ( ( ( k4_xboole_0 @ A @ B ) = ( k4_xboole_0 @ B @ A ) ) =>
% 7.31/7.52       ( ( A ) = ( B ) ) ))).
% 7.31/7.52  thf(zf_stmt_0, negated_conjecture,
% 7.31/7.52    (~( ![A:$i,B:$i]:
% 7.31/7.52        ( ( ( k4_xboole_0 @ A @ B ) = ( k4_xboole_0 @ B @ A ) ) =>
% 7.31/7.52          ( ( A ) = ( B ) ) ) )),
% 7.31/7.52    inference('cnf.neg', [status(esa)], [t32_xboole_1])).
% 7.31/7.52  thf('0', plain,
% 7.31/7.52      (((k4_xboole_0 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_B @ sk_A))),
% 7.31/7.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.31/7.52  thf(t2_tarski, axiom,
% 7.31/7.52    (![A:$i,B:$i]:
% 7.31/7.52     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 7.31/7.52       ( ( A ) = ( B ) ) ))).
% 7.31/7.52  thf('1', plain,
% 7.31/7.52      (![X6 : $i, X7 : $i]:
% 7.31/7.52         (((X7) = (X6))
% 7.31/7.52          | (r2_hidden @ (sk_C @ X6 @ X7) @ X6)
% 7.31/7.52          | (r2_hidden @ (sk_C @ X6 @ X7) @ X7))),
% 7.31/7.52      inference('cnf', [status(esa)], [t2_tarski])).
% 7.31/7.52  thf(d5_xboole_0, axiom,
% 7.31/7.52    (![A:$i,B:$i,C:$i]:
% 7.31/7.52     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 7.31/7.52       ( ![D:$i]:
% 7.31/7.52         ( ( r2_hidden @ D @ C ) <=>
% 7.31/7.52           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 7.31/7.52  thf('2', plain,
% 7.31/7.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.31/7.52         (~ (r2_hidden @ X0 @ X1)
% 7.31/7.52          | (r2_hidden @ X0 @ X2)
% 7.31/7.52          | (r2_hidden @ X0 @ X3)
% 7.31/7.52          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 7.31/7.52      inference('cnf', [status(esa)], [d5_xboole_0])).
% 7.31/7.52  thf('3', plain,
% 7.31/7.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.31/7.52         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 7.31/7.52          | (r2_hidden @ X0 @ X2)
% 7.31/7.52          | ~ (r2_hidden @ X0 @ X1))),
% 7.31/7.52      inference('simplify', [status(thm)], ['2'])).
% 7.31/7.52  thf('4', plain,
% 7.31/7.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.31/7.52         ((r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 7.31/7.52          | ((X1) = (X0))
% 7.31/7.52          | (r2_hidden @ (sk_C @ X0 @ X1) @ X2)
% 7.31/7.52          | (r2_hidden @ (sk_C @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X2)))),
% 7.31/7.52      inference('sup-', [status(thm)], ['1', '3'])).
% 7.31/7.52  thf('5', plain,
% 7.31/7.52      (((k4_xboole_0 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_B @ sk_A))),
% 7.31/7.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.31/7.52  thf('6', plain,
% 7.31/7.52      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 7.31/7.52         (~ (r2_hidden @ X4 @ X3)
% 7.31/7.52          | (r2_hidden @ X4 @ X1)
% 7.31/7.52          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 7.31/7.52      inference('cnf', [status(esa)], [d5_xboole_0])).
% 7.31/7.52  thf('7', plain,
% 7.31/7.52      (![X1 : $i, X2 : $i, X4 : $i]:
% 7.31/7.52         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 7.31/7.52      inference('simplify', [status(thm)], ['6'])).
% 7.31/7.52  thf('8', plain,
% 7.31/7.52      (![X0 : $i]:
% 7.31/7.52         (~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_A @ sk_B))
% 7.31/7.52          | (r2_hidden @ X0 @ sk_B))),
% 7.31/7.52      inference('sup-', [status(thm)], ['5', '7'])).
% 7.31/7.52  thf('9', plain,
% 7.31/7.52      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 7.31/7.52         (~ (r2_hidden @ X4 @ X3)
% 7.31/7.52          | ~ (r2_hidden @ X4 @ X2)
% 7.31/7.52          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 7.31/7.52      inference('cnf', [status(esa)], [d5_xboole_0])).
% 7.31/7.52  thf('10', plain,
% 7.31/7.52      (![X1 : $i, X2 : $i, X4 : $i]:
% 7.31/7.52         (~ (r2_hidden @ X4 @ X2)
% 7.31/7.52          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 7.31/7.52      inference('simplify', [status(thm)], ['9'])).
% 7.31/7.52  thf('11', plain,
% 7.31/7.52      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_A @ sk_B))),
% 7.31/7.52      inference('clc', [status(thm)], ['8', '10'])).
% 7.31/7.52  thf('12', plain,
% 7.31/7.52      (![X0 : $i]:
% 7.31/7.52         ((r2_hidden @ (sk_C @ sk_A @ X0) @ sk_B)
% 7.31/7.52          | ((X0) = (sk_A))
% 7.31/7.52          | (r2_hidden @ (sk_C @ sk_A @ X0) @ X0))),
% 7.31/7.52      inference('sup-', [status(thm)], ['4', '11'])).
% 7.31/7.52  thf('13', plain,
% 7.31/7.52      ((((sk_B) = (sk_A)) | (r2_hidden @ (sk_C @ sk_A @ sk_B) @ sk_B))),
% 7.31/7.52      inference('eq_fact', [status(thm)], ['12'])).
% 7.31/7.52  thf('14', plain, (((sk_A) != (sk_B))),
% 7.31/7.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.31/7.52  thf('15', plain, ((r2_hidden @ (sk_C @ sk_A @ sk_B) @ sk_B)),
% 7.31/7.52      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 7.31/7.52  thf('16', plain,
% 7.31/7.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.31/7.52         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 7.31/7.52          | (r2_hidden @ X0 @ X2)
% 7.31/7.52          | ~ (r2_hidden @ X0 @ X1))),
% 7.31/7.52      inference('simplify', [status(thm)], ['2'])).
% 7.31/7.52  thf('17', plain,
% 7.31/7.52      (![X0 : $i]:
% 7.31/7.52         ((r2_hidden @ (sk_C @ sk_A @ sk_B) @ X0)
% 7.31/7.52          | (r2_hidden @ (sk_C @ sk_A @ sk_B) @ (k4_xboole_0 @ sk_B @ X0)))),
% 7.31/7.52      inference('sup-', [status(thm)], ['15', '16'])).
% 7.31/7.52  thf('18', plain,
% 7.31/7.52      (((r2_hidden @ (sk_C @ sk_A @ sk_B) @ (k4_xboole_0 @ sk_A @ sk_B))
% 7.31/7.52        | (r2_hidden @ (sk_C @ sk_A @ sk_B) @ sk_A))),
% 7.31/7.52      inference('sup+', [status(thm)], ['0', '17'])).
% 7.31/7.52  thf('19', plain,
% 7.31/7.52      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_A @ sk_B))),
% 7.31/7.52      inference('clc', [status(thm)], ['8', '10'])).
% 7.31/7.52  thf('20', plain, ((r2_hidden @ (sk_C @ sk_A @ sk_B) @ sk_A)),
% 7.31/7.52      inference('clc', [status(thm)], ['18', '19'])).
% 7.31/7.52  thf('21', plain,
% 7.31/7.52      (![X6 : $i, X7 : $i]:
% 7.31/7.52         (((X7) = (X6))
% 7.31/7.52          | ~ (r2_hidden @ (sk_C @ X6 @ X7) @ X6)
% 7.31/7.52          | ~ (r2_hidden @ (sk_C @ X6 @ X7) @ X7))),
% 7.31/7.52      inference('cnf', [status(esa)], [t2_tarski])).
% 7.31/7.52  thf('22', plain,
% 7.31/7.52      ((~ (r2_hidden @ (sk_C @ sk_A @ sk_B) @ sk_B) | ((sk_B) = (sk_A)))),
% 7.31/7.52      inference('sup-', [status(thm)], ['20', '21'])).
% 7.31/7.52  thf('23', plain, ((r2_hidden @ (sk_C @ sk_A @ sk_B) @ sk_B)),
% 7.31/7.52      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 7.31/7.52  thf('24', plain, (((sk_B) = (sk_A))),
% 7.31/7.52      inference('demod', [status(thm)], ['22', '23'])).
% 7.31/7.52  thf('25', plain, (((sk_A) != (sk_B))),
% 7.31/7.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.31/7.52  thf('26', plain, ($false),
% 7.31/7.52      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 7.31/7.52  
% 7.31/7.52  % SZS output end Refutation
% 7.31/7.52  
% 7.36/7.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
