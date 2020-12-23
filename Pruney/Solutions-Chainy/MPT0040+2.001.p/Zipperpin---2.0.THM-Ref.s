%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rH4DQrjOu8

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:59 EST 2020

% Result     : Theorem 17.55s
% Output     : Refutation 17.55s
% Verified   : 
% Statistics : Number of formulae       :   33 (  40 expanded)
%              Number of leaves         :   10 (  16 expanded)
%              Depth                    :   10
%              Number of atoms          :  273 ( 348 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t33_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('3',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ sk_A @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k4_xboole_0 @ sk_A @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ( r2_hidden @ X4 @ X7 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('10',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ sk_A @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k4_xboole_0 @ sk_A @ X0 ) ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k4_xboole_0 @ sk_A @ X0 ) ) @ ( k4_xboole_0 @ sk_B @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k4_xboole_0 @ sk_A @ X1 ) ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ sk_A @ X1 ) @ ( k4_xboole_0 @ sk_B @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ sk_A @ X1 ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ sk_A @ X1 ) @ ( k4_xboole_0 @ sk_B @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k4_xboole_0 @ sk_A @ X1 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('17',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ sk_A @ X0 ) @ ( k4_xboole_0 @ sk_B @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ sk_A @ X0 ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ X0 ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    $false ),
    inference(demod,[status(thm)],['0','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rH4DQrjOu8
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:18:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 17.55/17.75  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 17.55/17.75  % Solved by: fo/fo7.sh
% 17.55/17.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 17.55/17.75  % done 21589 iterations in 17.285s
% 17.55/17.75  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 17.55/17.75  % SZS output start Refutation
% 17.55/17.75  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 17.55/17.75  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 17.55/17.75  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 17.55/17.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 17.55/17.75  thf(sk_B_type, type, sk_B: $i).
% 17.55/17.75  thf(sk_C_1_type, type, sk_C_1: $i).
% 17.55/17.75  thf(sk_A_type, type, sk_A: $i).
% 17.55/17.75  thf(t33_xboole_1, conjecture,
% 17.55/17.75    (![A:$i,B:$i,C:$i]:
% 17.55/17.75     ( ( r1_tarski @ A @ B ) =>
% 17.55/17.75       ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ))).
% 17.55/17.75  thf(zf_stmt_0, negated_conjecture,
% 17.55/17.75    (~( ![A:$i,B:$i,C:$i]:
% 17.55/17.75        ( ( r1_tarski @ A @ B ) =>
% 17.55/17.75          ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ) )),
% 17.55/17.75    inference('cnf.neg', [status(esa)], [t33_xboole_1])).
% 17.55/17.75  thf('0', plain,
% 17.55/17.75      (~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C_1) @ 
% 17.55/17.75          (k4_xboole_0 @ sk_B @ sk_C_1))),
% 17.55/17.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.55/17.75  thf(d3_tarski, axiom,
% 17.55/17.75    (![A:$i,B:$i]:
% 17.55/17.75     ( ( r1_tarski @ A @ B ) <=>
% 17.55/17.75       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 17.55/17.75  thf('1', plain,
% 17.55/17.75      (![X1 : $i, X3 : $i]:
% 17.55/17.75         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 17.55/17.75      inference('cnf', [status(esa)], [d3_tarski])).
% 17.55/17.75  thf(d5_xboole_0, axiom,
% 17.55/17.75    (![A:$i,B:$i,C:$i]:
% 17.55/17.75     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 17.55/17.75       ( ![D:$i]:
% 17.55/17.75         ( ( r2_hidden @ D @ C ) <=>
% 17.55/17.75           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 17.55/17.75  thf('2', plain,
% 17.55/17.75      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 17.55/17.75         (~ (r2_hidden @ X8 @ X7)
% 17.55/17.75          | (r2_hidden @ X8 @ X5)
% 17.55/17.75          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 17.55/17.75      inference('cnf', [status(esa)], [d5_xboole_0])).
% 17.55/17.75  thf('3', plain,
% 17.55/17.75      (![X5 : $i, X6 : $i, X8 : $i]:
% 17.55/17.75         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 17.55/17.75      inference('simplify', [status(thm)], ['2'])).
% 17.55/17.75  thf('4', plain,
% 17.55/17.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.55/17.75         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 17.55/17.75          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 17.55/17.75      inference('sup-', [status(thm)], ['1', '3'])).
% 17.55/17.75  thf('5', plain, ((r1_tarski @ sk_A @ sk_B)),
% 17.55/17.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.55/17.75  thf('6', plain,
% 17.55/17.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.55/17.75         (~ (r2_hidden @ X0 @ X1)
% 17.55/17.75          | (r2_hidden @ X0 @ X2)
% 17.55/17.75          | ~ (r1_tarski @ X1 @ X2))),
% 17.55/17.75      inference('cnf', [status(esa)], [d3_tarski])).
% 17.55/17.75  thf('7', plain,
% 17.55/17.75      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 17.55/17.75      inference('sup-', [status(thm)], ['5', '6'])).
% 17.55/17.75  thf('8', plain,
% 17.55/17.75      (![X0 : $i, X1 : $i]:
% 17.55/17.75         ((r1_tarski @ (k4_xboole_0 @ sk_A @ X0) @ X1)
% 17.55/17.75          | (r2_hidden @ (sk_C @ X1 @ (k4_xboole_0 @ sk_A @ X0)) @ sk_B))),
% 17.55/17.75      inference('sup-', [status(thm)], ['4', '7'])).
% 17.55/17.75  thf('9', plain,
% 17.55/17.75      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 17.55/17.75         (~ (r2_hidden @ X4 @ X5)
% 17.55/17.75          | (r2_hidden @ X4 @ X6)
% 17.55/17.75          | (r2_hidden @ X4 @ X7)
% 17.55/17.75          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 17.55/17.75      inference('cnf', [status(esa)], [d5_xboole_0])).
% 17.55/17.75  thf('10', plain,
% 17.55/17.75      (![X4 : $i, X5 : $i, X6 : $i]:
% 17.55/17.75         ((r2_hidden @ X4 @ (k4_xboole_0 @ X5 @ X6))
% 17.55/17.75          | (r2_hidden @ X4 @ X6)
% 17.55/17.75          | ~ (r2_hidden @ X4 @ X5))),
% 17.55/17.75      inference('simplify', [status(thm)], ['9'])).
% 17.55/17.75  thf('11', plain,
% 17.55/17.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.55/17.75         ((r1_tarski @ (k4_xboole_0 @ sk_A @ X0) @ X1)
% 17.55/17.75          | (r2_hidden @ (sk_C @ X1 @ (k4_xboole_0 @ sk_A @ X0)) @ X2)
% 17.55/17.75          | (r2_hidden @ (sk_C @ X1 @ (k4_xboole_0 @ sk_A @ X0)) @ 
% 17.55/17.75             (k4_xboole_0 @ sk_B @ X2)))),
% 17.55/17.75      inference('sup-', [status(thm)], ['8', '10'])).
% 17.55/17.75  thf('12', plain,
% 17.55/17.75      (![X1 : $i, X3 : $i]:
% 17.55/17.75         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 17.55/17.75      inference('cnf', [status(esa)], [d3_tarski])).
% 17.55/17.75  thf('13', plain,
% 17.55/17.75      (![X0 : $i, X1 : $i]:
% 17.55/17.75         ((r2_hidden @ 
% 17.55/17.75           (sk_C @ (k4_xboole_0 @ sk_B @ X0) @ (k4_xboole_0 @ sk_A @ X1)) @ X0)
% 17.55/17.75          | (r1_tarski @ (k4_xboole_0 @ sk_A @ X1) @ (k4_xboole_0 @ sk_B @ X0))
% 17.55/17.75          | (r1_tarski @ (k4_xboole_0 @ sk_A @ X1) @ (k4_xboole_0 @ sk_B @ X0)))),
% 17.55/17.75      inference('sup-', [status(thm)], ['11', '12'])).
% 17.55/17.75  thf('14', plain,
% 17.55/17.75      (![X0 : $i, X1 : $i]:
% 17.55/17.75         ((r1_tarski @ (k4_xboole_0 @ sk_A @ X1) @ (k4_xboole_0 @ sk_B @ X0))
% 17.55/17.75          | (r2_hidden @ 
% 17.55/17.75             (sk_C @ (k4_xboole_0 @ sk_B @ X0) @ (k4_xboole_0 @ sk_A @ X1)) @ 
% 17.55/17.75             X0))),
% 17.55/17.75      inference('simplify', [status(thm)], ['13'])).
% 17.55/17.75  thf('15', plain,
% 17.55/17.75      (![X1 : $i, X3 : $i]:
% 17.55/17.75         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 17.55/17.75      inference('cnf', [status(esa)], [d3_tarski])).
% 17.55/17.75  thf('16', plain,
% 17.55/17.75      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 17.55/17.75         (~ (r2_hidden @ X8 @ X7)
% 17.55/17.75          | ~ (r2_hidden @ X8 @ X6)
% 17.55/17.75          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 17.55/17.75      inference('cnf', [status(esa)], [d5_xboole_0])).
% 17.55/17.75  thf('17', plain,
% 17.55/17.75      (![X5 : $i, X6 : $i, X8 : $i]:
% 17.55/17.75         (~ (r2_hidden @ X8 @ X6)
% 17.55/17.75          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 17.55/17.75      inference('simplify', [status(thm)], ['16'])).
% 17.55/17.75  thf('18', plain,
% 17.55/17.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.55/17.75         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 17.55/17.75          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 17.55/17.75      inference('sup-', [status(thm)], ['15', '17'])).
% 17.55/17.75  thf('19', plain,
% 17.55/17.75      (![X0 : $i]:
% 17.55/17.75         ((r1_tarski @ (k4_xboole_0 @ sk_A @ X0) @ (k4_xboole_0 @ sk_B @ X0))
% 17.55/17.75          | (r1_tarski @ (k4_xboole_0 @ sk_A @ X0) @ (k4_xboole_0 @ sk_B @ X0)))),
% 17.55/17.75      inference('sup-', [status(thm)], ['14', '18'])).
% 17.55/17.75  thf('20', plain,
% 17.55/17.75      (![X0 : $i]:
% 17.55/17.75         (r1_tarski @ (k4_xboole_0 @ sk_A @ X0) @ (k4_xboole_0 @ sk_B @ X0))),
% 17.55/17.75      inference('simplify', [status(thm)], ['19'])).
% 17.55/17.75  thf('21', plain, ($false), inference('demod', [status(thm)], ['0', '20'])).
% 17.55/17.75  
% 17.55/17.75  % SZS output end Refutation
% 17.55/17.75  
% 17.55/17.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
