%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7HZU4LzDql

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:23 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :   33 (  40 expanded)
%              Number of leaves         :   12 (  17 expanded)
%              Depth                    :   11
%              Number of atoms          :  227 ( 325 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t77_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ( r1_tarski @ A @ C )
          & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('4',plain,(
    r1_tarski @ sk_A @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_2 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_A ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X6 )
      | ( r2_hidden @ X4 @ X7 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('9',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ sk_A ) @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_A ) @ ( k3_xboole_0 @ X1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_C_2 ) )
      | ( r1_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_C_2 ) )
      | ( r1_xboole_0 @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('14',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r1_xboole_0 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C_2 ) )
      | ( r1_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C_2 ) )
      | ( r1_xboole_0 @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['1','17'])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['0','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7HZU4LzDql
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:19:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.22/0.35  % Python version: Python 3.6.8
% 0.22/0.36  % Running in FO mode
% 0.90/1.10  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.90/1.10  % Solved by: fo/fo7.sh
% 0.90/1.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.10  % done 1255 iterations in 0.627s
% 0.90/1.10  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.90/1.10  % SZS output start Refutation
% 0.90/1.10  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.90/1.10  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.10  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.90/1.10  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.90/1.10  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.10  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.10  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.90/1.10  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.90/1.10  thf(t77_xboole_1, conjecture,
% 0.90/1.10    (![A:$i,B:$i,C:$i]:
% 0.90/1.10     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.90/1.10          ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 0.90/1.10  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.10    (~( ![A:$i,B:$i,C:$i]:
% 0.90/1.10        ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.90/1.10             ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )),
% 0.90/1.10    inference('cnf.neg', [status(esa)], [t77_xboole_1])).
% 0.90/1.10  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('1', plain, ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_2))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf(t3_xboole_0, axiom,
% 0.90/1.10    (![A:$i,B:$i]:
% 0.90/1.10     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.90/1.10            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.90/1.10       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.90/1.10            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.90/1.10  thf('2', plain,
% 0.90/1.10      (![X10 : $i, X11 : $i]:
% 0.90/1.10         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C_1 @ X11 @ X10) @ X11))),
% 0.90/1.10      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.90/1.10  thf('3', plain,
% 0.90/1.10      (![X10 : $i, X11 : $i]:
% 0.90/1.10         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C_1 @ X11 @ X10) @ X10))),
% 0.90/1.10      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.90/1.10  thf('4', plain, ((r1_tarski @ sk_A @ sk_C_2)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf(d3_tarski, axiom,
% 0.90/1.10    (![A:$i,B:$i]:
% 0.90/1.10     ( ( r1_tarski @ A @ B ) <=>
% 0.90/1.10       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.90/1.10  thf('5', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.10         (~ (r2_hidden @ X0 @ X1)
% 0.90/1.10          | (r2_hidden @ X0 @ X2)
% 0.90/1.10          | ~ (r1_tarski @ X1 @ X2))),
% 0.90/1.10      inference('cnf', [status(esa)], [d3_tarski])).
% 0.90/1.10  thf('6', plain,
% 0.90/1.10      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_2) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.90/1.10      inference('sup-', [status(thm)], ['4', '5'])).
% 0.90/1.10  thf('7', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         ((r1_xboole_0 @ sk_A @ X0)
% 0.90/1.10          | (r2_hidden @ (sk_C_1 @ X0 @ sk_A) @ sk_C_2))),
% 0.90/1.10      inference('sup-', [status(thm)], ['3', '6'])).
% 0.90/1.10  thf(d4_xboole_0, axiom,
% 0.90/1.10    (![A:$i,B:$i,C:$i]:
% 0.90/1.10     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.90/1.10       ( ![D:$i]:
% 0.90/1.10         ( ( r2_hidden @ D @ C ) <=>
% 0.90/1.10           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.90/1.10  thf('8', plain,
% 0.90/1.10      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.90/1.10         (~ (r2_hidden @ X4 @ X5)
% 0.90/1.10          | ~ (r2_hidden @ X4 @ X6)
% 0.90/1.10          | (r2_hidden @ X4 @ X7)
% 0.90/1.10          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 0.90/1.10      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.90/1.10  thf('9', plain,
% 0.90/1.10      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.90/1.10         ((r2_hidden @ X4 @ (k3_xboole_0 @ X5 @ X6))
% 0.90/1.10          | ~ (r2_hidden @ X4 @ X6)
% 0.90/1.10          | ~ (r2_hidden @ X4 @ X5))),
% 0.90/1.10      inference('simplify', [status(thm)], ['8'])).
% 0.90/1.10  thf('10', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         ((r1_xboole_0 @ sk_A @ X0)
% 0.90/1.10          | ~ (r2_hidden @ (sk_C_1 @ X0 @ sk_A) @ X1)
% 0.90/1.10          | (r2_hidden @ (sk_C_1 @ X0 @ sk_A) @ (k3_xboole_0 @ X1 @ sk_C_2)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['7', '9'])).
% 0.90/1.10  thf('11', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         ((r1_xboole_0 @ sk_A @ X0)
% 0.90/1.10          | (r2_hidden @ (sk_C_1 @ X0 @ sk_A) @ (k3_xboole_0 @ X0 @ sk_C_2))
% 0.90/1.10          | (r1_xboole_0 @ sk_A @ X0))),
% 0.90/1.10      inference('sup-', [status(thm)], ['2', '10'])).
% 0.90/1.10  thf('12', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         ((r2_hidden @ (sk_C_1 @ X0 @ sk_A) @ (k3_xboole_0 @ X0 @ sk_C_2))
% 0.90/1.10          | (r1_xboole_0 @ sk_A @ X0))),
% 0.90/1.10      inference('simplify', [status(thm)], ['11'])).
% 0.90/1.10  thf('13', plain,
% 0.90/1.10      (![X10 : $i, X11 : $i]:
% 0.90/1.10         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C_1 @ X11 @ X10) @ X10))),
% 0.90/1.10      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.90/1.10  thf('14', plain,
% 0.90/1.10      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.90/1.10         (~ (r2_hidden @ X12 @ X10)
% 0.90/1.10          | ~ (r2_hidden @ X12 @ X13)
% 0.90/1.10          | ~ (r1_xboole_0 @ X10 @ X13))),
% 0.90/1.10      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.90/1.10  thf('15', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.10         ((r1_xboole_0 @ X0 @ X1)
% 0.90/1.10          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.90/1.10          | ~ (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X2))),
% 0.90/1.10      inference('sup-', [status(thm)], ['13', '14'])).
% 0.90/1.10  thf('16', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         ((r1_xboole_0 @ sk_A @ X0)
% 0.90/1.10          | ~ (r1_xboole_0 @ sk_A @ (k3_xboole_0 @ X0 @ sk_C_2))
% 0.90/1.10          | (r1_xboole_0 @ sk_A @ X0))),
% 0.90/1.10      inference('sup-', [status(thm)], ['12', '15'])).
% 0.90/1.10  thf('17', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         (~ (r1_xboole_0 @ sk_A @ (k3_xboole_0 @ X0 @ sk_C_2))
% 0.90/1.10          | (r1_xboole_0 @ sk_A @ X0))),
% 0.90/1.10      inference('simplify', [status(thm)], ['16'])).
% 0.90/1.10  thf('18', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.90/1.10      inference('sup-', [status(thm)], ['1', '17'])).
% 0.90/1.10  thf('19', plain, ($false), inference('demod', [status(thm)], ['0', '18'])).
% 0.90/1.10  
% 0.90/1.10  % SZS output end Refutation
% 0.90/1.10  
% 0.90/1.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
