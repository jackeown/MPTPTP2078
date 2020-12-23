%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.efOstdqLDG

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:48 EST 2020

% Result     : Theorem 4.39s
% Output     : Refutation 4.39s
% Verified   : 
% Statistics : Number of formulae       :   39 (  48 expanded)
%              Number of leaves         :   13 (  19 expanded)
%              Depth                    :   11
%              Number of atoms          :  332 ( 457 expanded)
%              Number of equality atoms :   29 (  38 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t87_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k2_xboole_0 @ ( k4_xboole_0 @ C @ A ) @ B )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ C @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_xboole_0 @ A @ B )
       => ( ( k2_xboole_0 @ ( k4_xboole_0 @ C @ A ) @ B )
          = ( k4_xboole_0 @ ( k2_xboole_0 @ C @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t87_xboole_1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_A ) @ sk_B )
 != ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('3',plain,(
    ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_C @ sk_A ) )
 != ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['4'])).

thf('7',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['4'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('16',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ sk_A ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,
    ( ( sk_B
      = ( k4_xboole_0 @ sk_B @ sk_A ) )
    | ( sk_B
      = ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','18'])).

thf('20',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t42_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ ( k4_xboole_0 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ X0 ) @ sk_A )
      = ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_C @ sk_A ) )
 != ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','22'])).

thf('24',plain,(
    $false ),
    inference(simplify,[status(thm)],['23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.efOstdqLDG
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:37:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.39/4.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.39/4.58  % Solved by: fo/fo7.sh
% 4.39/4.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.39/4.58  % done 3030 iterations in 4.127s
% 4.39/4.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.39/4.58  % SZS output start Refutation
% 4.39/4.58  thf(sk_B_type, type, sk_B: $i).
% 4.39/4.58  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 4.39/4.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.39/4.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.39/4.58  thf(sk_A_type, type, sk_A: $i).
% 4.39/4.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.39/4.58  thf(sk_C_type, type, sk_C: $i).
% 4.39/4.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 4.39/4.58  thf(t87_xboole_1, conjecture,
% 4.39/4.58    (![A:$i,B:$i,C:$i]:
% 4.39/4.58     ( ( r1_xboole_0 @ A @ B ) =>
% 4.39/4.58       ( ( k2_xboole_0 @ ( k4_xboole_0 @ C @ A ) @ B ) =
% 4.39/4.58         ( k4_xboole_0 @ ( k2_xboole_0 @ C @ B ) @ A ) ) ))).
% 4.39/4.58  thf(zf_stmt_0, negated_conjecture,
% 4.39/4.58    (~( ![A:$i,B:$i,C:$i]:
% 4.39/4.58        ( ( r1_xboole_0 @ A @ B ) =>
% 4.39/4.58          ( ( k2_xboole_0 @ ( k4_xboole_0 @ C @ A ) @ B ) =
% 4.39/4.58            ( k4_xboole_0 @ ( k2_xboole_0 @ C @ B ) @ A ) ) ) )),
% 4.39/4.58    inference('cnf.neg', [status(esa)], [t87_xboole_1])).
% 4.39/4.58  thf('0', plain,
% 4.39/4.58      (((k2_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_A) @ sk_B)
% 4.39/4.58         != (k4_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_B) @ sk_A))),
% 4.39/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.58  thf(commutativity_k2_xboole_0, axiom,
% 4.39/4.58    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 4.39/4.58  thf('1', plain,
% 4.39/4.58      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.39/4.58      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.39/4.58  thf('2', plain,
% 4.39/4.58      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.39/4.58      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.39/4.58  thf('3', plain,
% 4.39/4.58      (((k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_C @ sk_A))
% 4.39/4.58         != (k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C) @ sk_A))),
% 4.39/4.58      inference('demod', [status(thm)], ['0', '1', '2'])).
% 4.39/4.58  thf(d5_xboole_0, axiom,
% 4.39/4.58    (![A:$i,B:$i,C:$i]:
% 4.39/4.58     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 4.39/4.58       ( ![D:$i]:
% 4.39/4.58         ( ( r2_hidden @ D @ C ) <=>
% 4.39/4.58           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 4.39/4.58  thf('4', plain,
% 4.39/4.58      (![X3 : $i, X4 : $i, X7 : $i]:
% 4.39/4.58         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 4.39/4.58          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 4.39/4.58          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 4.39/4.58      inference('cnf', [status(esa)], [d5_xboole_0])).
% 4.39/4.58  thf('5', plain,
% 4.39/4.58      (![X0 : $i, X1 : $i]:
% 4.39/4.58         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 4.39/4.58          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 4.39/4.58      inference('eq_fact', [status(thm)], ['4'])).
% 4.39/4.58  thf('6', plain,
% 4.39/4.58      (![X0 : $i, X1 : $i]:
% 4.39/4.58         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 4.39/4.58          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 4.39/4.58      inference('eq_fact', [status(thm)], ['4'])).
% 4.39/4.58  thf('7', plain,
% 4.39/4.58      (![X3 : $i, X4 : $i, X7 : $i]:
% 4.39/4.58         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 4.39/4.58          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 4.39/4.58          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 4.39/4.58          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 4.39/4.58      inference('cnf', [status(esa)], [d5_xboole_0])).
% 4.39/4.58  thf('8', plain,
% 4.39/4.58      (![X0 : $i, X1 : $i]:
% 4.39/4.58         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 4.39/4.58          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 4.39/4.58          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 4.39/4.58          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 4.39/4.58      inference('sup-', [status(thm)], ['6', '7'])).
% 4.39/4.58  thf('9', plain,
% 4.39/4.58      (![X0 : $i, X1 : $i]:
% 4.39/4.58         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 4.39/4.58          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 4.39/4.58          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 4.39/4.58      inference('simplify', [status(thm)], ['8'])).
% 4.39/4.58  thf('10', plain,
% 4.39/4.58      (![X0 : $i, X1 : $i]:
% 4.39/4.58         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 4.39/4.58          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 4.39/4.58      inference('eq_fact', [status(thm)], ['4'])).
% 4.39/4.58  thf('11', plain,
% 4.39/4.58      (![X0 : $i, X1 : $i]:
% 4.39/4.58         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 4.39/4.58          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 4.39/4.58      inference('clc', [status(thm)], ['9', '10'])).
% 4.39/4.58  thf('12', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 4.39/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.58  thf(t83_xboole_1, axiom,
% 4.39/4.58    (![A:$i,B:$i]:
% 4.39/4.58     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 4.39/4.58  thf('13', plain,
% 4.39/4.58      (![X11 : $i, X12 : $i]:
% 4.39/4.58         (((k4_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_xboole_0 @ X11 @ X12))),
% 4.39/4.58      inference('cnf', [status(esa)], [t83_xboole_1])).
% 4.39/4.58  thf('14', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 4.39/4.58      inference('sup-', [status(thm)], ['12', '13'])).
% 4.39/4.58  thf('15', plain,
% 4.39/4.58      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 4.39/4.58         (~ (r2_hidden @ X6 @ X5)
% 4.39/4.58          | ~ (r2_hidden @ X6 @ X4)
% 4.39/4.58          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 4.39/4.58      inference('cnf', [status(esa)], [d5_xboole_0])).
% 4.39/4.58  thf('16', plain,
% 4.39/4.58      (![X3 : $i, X4 : $i, X6 : $i]:
% 4.39/4.58         (~ (r2_hidden @ X6 @ X4)
% 4.39/4.58          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 4.39/4.58      inference('simplify', [status(thm)], ['15'])).
% 4.39/4.58  thf('17', plain,
% 4.39/4.58      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B))),
% 4.39/4.58      inference('sup-', [status(thm)], ['14', '16'])).
% 4.39/4.58  thf('18', plain,
% 4.39/4.58      (![X0 : $i]:
% 4.39/4.58         (((X0) = (k4_xboole_0 @ X0 @ sk_A))
% 4.39/4.58          | ~ (r2_hidden @ (sk_D @ X0 @ sk_A @ X0) @ sk_B))),
% 4.39/4.58      inference('sup-', [status(thm)], ['11', '17'])).
% 4.39/4.58  thf('19', plain,
% 4.39/4.58      ((((sk_B) = (k4_xboole_0 @ sk_B @ sk_A))
% 4.39/4.58        | ((sk_B) = (k4_xboole_0 @ sk_B @ sk_A)))),
% 4.39/4.58      inference('sup-', [status(thm)], ['5', '18'])).
% 4.39/4.58  thf('20', plain, (((sk_B) = (k4_xboole_0 @ sk_B @ sk_A))),
% 4.39/4.58      inference('simplify', [status(thm)], ['19'])).
% 4.39/4.58  thf(t42_xboole_1, axiom,
% 4.39/4.58    (![A:$i,B:$i,C:$i]:
% 4.39/4.58     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 4.39/4.58       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ))).
% 4.39/4.58  thf('21', plain,
% 4.39/4.58      (![X8 : $i, X9 : $i, X10 : $i]:
% 4.39/4.58         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X10) @ X9)
% 4.39/4.58           = (k2_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ (k4_xboole_0 @ X10 @ X9)))),
% 4.39/4.58      inference('cnf', [status(esa)], [t42_xboole_1])).
% 4.39/4.58  thf('22', plain,
% 4.39/4.58      (![X0 : $i]:
% 4.39/4.58         ((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ X0) @ sk_A)
% 4.39/4.58           = (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_A)))),
% 4.39/4.58      inference('sup+', [status(thm)], ['20', '21'])).
% 4.39/4.58  thf('23', plain,
% 4.39/4.58      (((k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_C @ sk_A))
% 4.39/4.58         != (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_C @ sk_A)))),
% 4.39/4.58      inference('demod', [status(thm)], ['3', '22'])).
% 4.39/4.58  thf('24', plain, ($false), inference('simplify', [status(thm)], ['23'])).
% 4.39/4.58  
% 4.39/4.58  % SZS output end Refutation
% 4.39/4.58  
% 4.39/4.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
