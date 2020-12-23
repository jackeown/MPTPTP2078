%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NKr4nQx7Kh

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:50 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   31 (  39 expanded)
%              Number of leaves         :   10 (  16 expanded)
%              Depth                    :   10
%              Number of atoms          :  205 ( 285 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t19_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ A @ C ) )
       => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t19_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ) ),
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

thf('2',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    r1_tarski @ sk_A @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X6 )
      | ( r2_hidden @ X4 @ X7 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('12',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k3_xboole_0 @ X1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,
    ( ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) )
    | ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['0','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.16  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.17  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NKr4nQx7Kh
% 0.18/0.38  % Computer   : n025.cluster.edu
% 0.18/0.38  % Model      : x86_64 x86_64
% 0.18/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.18/0.38  % Memory     : 8042.1875MB
% 0.18/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.18/0.38  % CPULimit   : 60
% 0.18/0.38  % DateTime   : Tue Dec  1 20:36:06 EST 2020
% 0.18/0.39  % CPUTime    : 
% 0.18/0.39  % Running portfolio for 600 s
% 0.18/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.18/0.39  % Number of cores: 8
% 0.18/0.39  % Python version: Python 3.6.8
% 0.18/0.39  % Running in FO mode
% 0.41/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.61  % Solved by: fo/fo7.sh
% 0.41/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.61  % done 313 iterations in 0.116s
% 0.41/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.61  % SZS output start Refutation
% 0.41/0.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.41/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.41/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.61  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.41/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.61  thf(t19_xboole_1, conjecture,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.41/0.61       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.41/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.41/0.61        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.41/0.61          ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )),
% 0.41/0.61    inference('cnf.neg', [status(esa)], [t19_xboole_1])).
% 0.41/0.61  thf('0', plain, (~ (r1_tarski @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(d3_tarski, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( r1_tarski @ A @ B ) <=>
% 0.41/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.41/0.61  thf('1', plain,
% 0.41/0.61      (![X1 : $i, X3 : $i]:
% 0.41/0.61         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.41/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.61  thf('2', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('3', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.61         (~ (r2_hidden @ X0 @ X1)
% 0.41/0.61          | (r2_hidden @ X0 @ X2)
% 0.41/0.61          | ~ (r1_tarski @ X1 @ X2))),
% 0.41/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.61  thf('4', plain,
% 0.41/0.61      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.41/0.61      inference('sup-', [status(thm)], ['2', '3'])).
% 0.41/0.61  thf('5', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((r1_tarski @ sk_A @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 0.41/0.61      inference('sup-', [status(thm)], ['1', '4'])).
% 0.41/0.61  thf('6', plain,
% 0.41/0.61      (![X1 : $i, X3 : $i]:
% 0.41/0.61         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.41/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.61  thf('7', plain, ((r1_tarski @ sk_A @ sk_C_1)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('8', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.61         (~ (r2_hidden @ X0 @ X1)
% 0.41/0.61          | (r2_hidden @ X0 @ X2)
% 0.41/0.61          | ~ (r1_tarski @ X1 @ X2))),
% 0.41/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.61  thf('9', plain,
% 0.41/0.61      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_1) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.41/0.61      inference('sup-', [status(thm)], ['7', '8'])).
% 0.41/0.61  thf('10', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((r1_tarski @ sk_A @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_C_1))),
% 0.41/0.61      inference('sup-', [status(thm)], ['6', '9'])).
% 0.41/0.61  thf(d4_xboole_0, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.41/0.61       ( ![D:$i]:
% 0.41/0.61         ( ( r2_hidden @ D @ C ) <=>
% 0.41/0.61           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.41/0.61  thf('11', plain,
% 0.41/0.61      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.41/0.61         (~ (r2_hidden @ X4 @ X5)
% 0.41/0.61          | ~ (r2_hidden @ X4 @ X6)
% 0.41/0.61          | (r2_hidden @ X4 @ X7)
% 0.41/0.61          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 0.41/0.61      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.41/0.61  thf('12', plain,
% 0.41/0.61      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.41/0.61         ((r2_hidden @ X4 @ (k3_xboole_0 @ X5 @ X6))
% 0.41/0.61          | ~ (r2_hidden @ X4 @ X6)
% 0.41/0.61          | ~ (r2_hidden @ X4 @ X5))),
% 0.41/0.61      inference('simplify', [status(thm)], ['11'])).
% 0.41/0.61  thf('13', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         ((r1_tarski @ sk_A @ X0)
% 0.41/0.61          | ~ (r2_hidden @ (sk_C @ X0 @ sk_A) @ X1)
% 0.41/0.61          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ (k3_xboole_0 @ X1 @ sk_C_1)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['10', '12'])).
% 0.41/0.61  thf('14', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((r1_tarski @ sk_A @ X0)
% 0.41/0.61          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ (k3_xboole_0 @ sk_B @ sk_C_1))
% 0.41/0.61          | (r1_tarski @ sk_A @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['5', '13'])).
% 0.41/0.61  thf('15', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((r2_hidden @ (sk_C @ X0 @ sk_A) @ (k3_xboole_0 @ sk_B @ sk_C_1))
% 0.41/0.61          | (r1_tarski @ sk_A @ X0))),
% 0.41/0.61      inference('simplify', [status(thm)], ['14'])).
% 0.41/0.61  thf('16', plain,
% 0.41/0.61      (![X1 : $i, X3 : $i]:
% 0.41/0.61         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.41/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.61  thf('17', plain,
% 0.41/0.61      (((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1))
% 0.41/0.61        | (r1_tarski @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['15', '16'])).
% 0.41/0.61  thf('18', plain, ((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1))),
% 0.41/0.61      inference('simplify', [status(thm)], ['17'])).
% 0.41/0.61  thf('19', plain, ($false), inference('demod', [status(thm)], ['0', '18'])).
% 0.41/0.61  
% 0.41/0.61  % SZS output end Refutation
% 0.41/0.61  
% 0.41/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
