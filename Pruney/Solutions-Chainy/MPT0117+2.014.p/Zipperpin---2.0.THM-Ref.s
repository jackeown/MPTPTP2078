%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4d8aWs7mZL

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:48 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   31 (  41 expanded)
%              Number of leaves         :   10 (  17 expanded)
%              Depth                    :   10
%              Number of atoms          :  215 ( 317 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t110_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ C @ B ) )
       => ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t110_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ) ),
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

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ ( k5_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k5_xboole_0 @ X0 @ sk_C_1 ) ) @ X0 )
      | ( r1_tarski @ ( k5_xboole_0 @ X0 @ sk_C_1 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k5_xboole_0 @ X0 @ sk_C_1 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_xboole_0 @ X0 @ sk_C_1 ) @ sk_B )
      | ( r2_hidden @ ( sk_C @ sk_B @ ( k5_xboole_0 @ X0 @ sk_C_1 ) ) @ X0 )
      | ( r1_tarski @ ( k5_xboole_0 @ X0 @ sk_C_1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ sk_B @ ( k5_xboole_0 @ X0 @ sk_C_1 ) ) @ X0 )
      | ( r1_tarski @ ( k5_xboole_0 @ X0 @ sk_C_1 ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B )
    | ( r2_hidden @ ( sk_C @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    r2_hidden @ ( sk_C @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) ) @ sk_B ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['0','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4d8aWs7mZL
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:15:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.63  % Solved by: fo/fo7.sh
% 0.46/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.63  % done 138 iterations in 0.179s
% 0.46/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.63  % SZS output start Refutation
% 0.46/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.63  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.46/0.63  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.63  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.46/0.63  thf(t110_xboole_1, conjecture,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.46/0.63       ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 0.46/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.63    (~( ![A:$i,B:$i,C:$i]:
% 0.46/0.63        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.46/0.63          ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )),
% 0.46/0.63    inference('cnf.neg', [status(esa)], [t110_xboole_1])).
% 0.46/0.63  thf('0', plain, (~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(d3_tarski, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( r1_tarski @ A @ B ) <=>
% 0.46/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.46/0.63  thf('1', plain,
% 0.46/0.63      (![X1 : $i, X3 : $i]:
% 0.46/0.63         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.63  thf(t1_xboole_0, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.46/0.63       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.46/0.63  thf('2', plain,
% 0.46/0.63      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.46/0.63         ((r2_hidden @ X4 @ X5)
% 0.46/0.63          | (r2_hidden @ X4 @ X6)
% 0.46/0.63          | ~ (r2_hidden @ X4 @ (k5_xboole_0 @ X5 @ X6)))),
% 0.46/0.63      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.46/0.63  thf('3', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.63         ((r1_tarski @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 0.46/0.63          | (r2_hidden @ (sk_C @ X2 @ (k5_xboole_0 @ X1 @ X0)) @ X0)
% 0.46/0.63          | (r2_hidden @ (sk_C @ X2 @ (k5_xboole_0 @ X1 @ X0)) @ X1))),
% 0.46/0.63      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.63  thf('4', plain, ((r1_tarski @ sk_C_1 @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('5', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.63         (~ (r2_hidden @ X0 @ X1)
% 0.46/0.63          | (r2_hidden @ X0 @ X2)
% 0.46/0.63          | ~ (r1_tarski @ X1 @ X2))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.63  thf('6', plain,
% 0.46/0.63      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.46/0.63      inference('sup-', [status(thm)], ['4', '5'])).
% 0.46/0.63  thf('7', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         ((r2_hidden @ (sk_C @ X1 @ (k5_xboole_0 @ X0 @ sk_C_1)) @ X0)
% 0.46/0.63          | (r1_tarski @ (k5_xboole_0 @ X0 @ sk_C_1) @ X1)
% 0.46/0.63          | (r2_hidden @ (sk_C @ X1 @ (k5_xboole_0 @ X0 @ sk_C_1)) @ sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['3', '6'])).
% 0.46/0.63  thf('8', plain,
% 0.46/0.63      (![X1 : $i, X3 : $i]:
% 0.46/0.63         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.63  thf('9', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((r1_tarski @ (k5_xboole_0 @ X0 @ sk_C_1) @ sk_B)
% 0.46/0.63          | (r2_hidden @ (sk_C @ sk_B @ (k5_xboole_0 @ X0 @ sk_C_1)) @ X0)
% 0.46/0.63          | (r1_tarski @ (k5_xboole_0 @ X0 @ sk_C_1) @ sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['7', '8'])).
% 0.46/0.63  thf('10', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((r2_hidden @ (sk_C @ sk_B @ (k5_xboole_0 @ X0 @ sk_C_1)) @ X0)
% 0.46/0.63          | (r1_tarski @ (k5_xboole_0 @ X0 @ sk_C_1) @ sk_B))),
% 0.46/0.63      inference('simplify', [status(thm)], ['9'])).
% 0.46/0.63  thf('11', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('12', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.63         (~ (r2_hidden @ X0 @ X1)
% 0.46/0.63          | (r2_hidden @ X0 @ X2)
% 0.46/0.63          | ~ (r1_tarski @ X1 @ X2))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.63  thf('13', plain,
% 0.46/0.63      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['11', '12'])).
% 0.46/0.63  thf('14', plain,
% 0.46/0.63      (((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ sk_B)
% 0.46/0.63        | (r2_hidden @ (sk_C @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C_1)) @ sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['10', '13'])).
% 0.46/0.63  thf('15', plain, (~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('16', plain,
% 0.46/0.63      ((r2_hidden @ (sk_C @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C_1)) @ sk_B)),
% 0.46/0.63      inference('clc', [status(thm)], ['14', '15'])).
% 0.46/0.63  thf('17', plain,
% 0.46/0.63      (![X1 : $i, X3 : $i]:
% 0.46/0.63         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.63  thf('18', plain, ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 0.46/0.63      inference('sup-', [status(thm)], ['16', '17'])).
% 0.46/0.63  thf('19', plain, ($false), inference('demod', [status(thm)], ['0', '18'])).
% 0.46/0.63  
% 0.46/0.63  % SZS output end Refutation
% 0.46/0.63  
% 0.46/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
