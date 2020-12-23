%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fZwZuGbvcS

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:01 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   32 (  35 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    9
%              Number of atoms          :  173 ( 207 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('0',plain,(
    ! [X13: $i] :
      ( ( k3_xboole_0 @ X13 @ X13 )
      = X13 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

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
    ! [X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ X14 @ X15 )
      | ( r2_hidden @ ( sk_C_1 @ X15 @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t38_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
       => ( A = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t38_xboole_1])).

thf('2',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('7',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ X14 @ X15 )
      | ( r2_hidden @ ( sk_C_1 @ X15 @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ X0 ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup+',[status(thm)],['0','12'])).

thf('14',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fZwZuGbvcS
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:11:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.22/0.36  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 40 iterations in 0.023s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.22/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.49  thf(idempotence_k3_xboole_0, axiom,
% 0.22/0.49    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.22/0.49  thf('0', plain, (![X13 : $i]: ((k3_xboole_0 @ X13 @ X13) = (X13))),
% 0.22/0.49      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.22/0.49  thf(t3_xboole_0, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.22/0.49            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.49       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.22/0.49            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      (![X14 : $i, X15 : $i]:
% 0.22/0.49         ((r1_xboole_0 @ X14 @ X15) | (r2_hidden @ (sk_C_1 @ X15 @ X14) @ X14))),
% 0.22/0.49      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.49  thf(t38_xboole_1, conjecture,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.22/0.49       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i,B:$i]:
% 0.22/0.49        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.22/0.49          ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t38_xboole_1])).
% 0.22/0.49  thf('2', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(d3_tarski, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X0 @ X1)
% 0.22/0.49          | (r2_hidden @ X0 @ X2)
% 0.22/0.49          | ~ (r1_tarski @ X1 @ X2))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((r2_hidden @ X0 @ (k4_xboole_0 @ sk_B @ sk_A))
% 0.22/0.49          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((r1_xboole_0 @ sk_A @ X0)
% 0.22/0.49          | (r2_hidden @ (sk_C_1 @ X0 @ sk_A) @ (k4_xboole_0 @ sk_B @ sk_A)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['1', '4'])).
% 0.22/0.49  thf(d5_xboole_0, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.22/0.49       ( ![D:$i]:
% 0.22/0.49         ( ( r2_hidden @ D @ C ) <=>
% 0.22/0.49           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X8 @ X7)
% 0.22/0.49          | ~ (r2_hidden @ X8 @ X6)
% 0.22/0.49          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.22/0.49      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X8 @ X6)
% 0.22/0.49          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.22/0.49      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((r1_xboole_0 @ sk_A @ X0)
% 0.22/0.49          | ~ (r2_hidden @ (sk_C_1 @ X0 @ sk_A) @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['5', '7'])).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      (![X14 : $i, X15 : $i]:
% 0.22/0.49         ((r1_xboole_0 @ X14 @ X15) | (r2_hidden @ (sk_C_1 @ X15 @ X14) @ X14))),
% 0.22/0.49      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.49  thf('10', plain, (![X0 : $i]: (r1_xboole_0 @ sk_A @ X0)),
% 0.22/0.49      inference('clc', [status(thm)], ['8', '9'])).
% 0.22/0.49  thf(d7_xboole_0, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.22/0.49       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      (![X10 : $i, X11 : $i]:
% 0.22/0.49         (((k3_xboole_0 @ X10 @ X11) = (k1_xboole_0))
% 0.22/0.49          | ~ (r1_xboole_0 @ X10 @ X11))),
% 0.22/0.49      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.22/0.49  thf('12', plain, (![X0 : $i]: ((k3_xboole_0 @ sk_A @ X0) = (k1_xboole_0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.49  thf('13', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['0', '12'])).
% 0.22/0.49  thf('14', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('15', plain, ($false),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
