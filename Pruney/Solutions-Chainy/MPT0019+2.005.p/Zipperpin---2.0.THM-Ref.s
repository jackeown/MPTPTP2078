%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rqEeOcKcTj

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:47 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   30 (  55 expanded)
%              Number of leaves         :    9 (  19 expanded)
%              Depth                    :   11
%              Number of atoms          :  269 ( 598 expanded)
%              Number of equality atoms :   20 (  42 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X7: $i,X9: $i] :
      ( ( X9
        = ( k2_xboole_0 @ X7 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X5 @ X7 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X5 @ X7 ) @ X7 )
      | ( r2_hidden @ ( sk_D @ X9 @ X5 @ X7 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('2',plain,(
    ! [X5: $i,X7: $i,X9: $i] :
      ( ( X9
        = ( k2_xboole_0 @ X7 @ X5 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X5 @ X7 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X5 @ X7 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf(t12_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ A @ B )
       => ( ( k2_xboole_0 @ A @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_xboole_1])).

thf('7',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('12',plain,(
    ! [X5: $i,X7: $i,X9: $i] :
      ( ( X9
        = ( k2_xboole_0 @ X7 @ X5 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X5 @ X7 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X5 @ X7 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('13',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_A @ sk_B ) )
    | ~ ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ sk_B )
    | ( sk_B
      = ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ sk_B )
    | ( sk_B
      = ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ~ ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('17',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf('18',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rqEeOcKcTj
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:57:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.55  % Solved by: fo/fo7.sh
% 0.35/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.55  % done 116 iterations in 0.093s
% 0.35/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.55  % SZS output start Refutation
% 0.35/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.35/0.55  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.35/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.55  thf(d3_xboole_0, axiom,
% 0.35/0.55    (![A:$i,B:$i,C:$i]:
% 0.35/0.55     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.35/0.55       ( ![D:$i]:
% 0.35/0.55         ( ( r2_hidden @ D @ C ) <=>
% 0.35/0.55           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.35/0.55  thf('0', plain,
% 0.35/0.55      (![X5 : $i, X7 : $i, X9 : $i]:
% 0.35/0.55         (((X9) = (k2_xboole_0 @ X7 @ X5))
% 0.35/0.55          | (r2_hidden @ (sk_D @ X9 @ X5 @ X7) @ X5)
% 0.35/0.55          | (r2_hidden @ (sk_D @ X9 @ X5 @ X7) @ X7)
% 0.35/0.55          | (r2_hidden @ (sk_D @ X9 @ X5 @ X7) @ X9))),
% 0.35/0.55      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.35/0.55  thf('1', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]:
% 0.35/0.55         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.35/0.55          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.35/0.55          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 0.35/0.55      inference('eq_fact', [status(thm)], ['0'])).
% 0.35/0.55  thf('2', plain,
% 0.35/0.55      (![X5 : $i, X7 : $i, X9 : $i]:
% 0.35/0.55         (((X9) = (k2_xboole_0 @ X7 @ X5))
% 0.35/0.55          | ~ (r2_hidden @ (sk_D @ X9 @ X5 @ X7) @ X5)
% 0.35/0.55          | ~ (r2_hidden @ (sk_D @ X9 @ X5 @ X7) @ X9))),
% 0.35/0.55      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.35/0.55  thf('3', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]:
% 0.35/0.55         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 0.35/0.55          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.35/0.55          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.35/0.55          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.35/0.55  thf('4', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]:
% 0.35/0.55         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.35/0.55          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.35/0.55          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 0.35/0.55      inference('simplify', [status(thm)], ['3'])).
% 0.35/0.55  thf('5', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]:
% 0.35/0.55         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.35/0.55          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.35/0.55          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 0.35/0.55      inference('eq_fact', [status(thm)], ['0'])).
% 0.35/0.55  thf('6', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]:
% 0.35/0.55         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 0.35/0.55          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 0.35/0.55      inference('clc', [status(thm)], ['4', '5'])).
% 0.35/0.55  thf(t12_xboole_1, conjecture,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.35/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.55    (~( ![A:$i,B:$i]:
% 0.35/0.55        ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ) )),
% 0.35/0.55    inference('cnf.neg', [status(esa)], [t12_xboole_1])).
% 0.35/0.55  thf('7', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(d3_tarski, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( r1_tarski @ A @ B ) <=>
% 0.35/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.35/0.55  thf('8', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.55         (~ (r2_hidden @ X0 @ X1)
% 0.35/0.55          | (r2_hidden @ X0 @ X2)
% 0.35/0.55          | ~ (r1_tarski @ X1 @ X2))),
% 0.35/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.35/0.55  thf('9', plain,
% 0.35/0.55      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.35/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.35/0.55  thf('10', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         (((X0) = (k2_xboole_0 @ sk_A @ X0))
% 0.35/0.55          | (r2_hidden @ (sk_D @ X0 @ X0 @ sk_A) @ sk_B))),
% 0.35/0.55      inference('sup-', [status(thm)], ['6', '9'])).
% 0.35/0.55  thf('11', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         (((X0) = (k2_xboole_0 @ sk_A @ X0))
% 0.35/0.55          | (r2_hidden @ (sk_D @ X0 @ X0 @ sk_A) @ sk_B))),
% 0.35/0.55      inference('sup-', [status(thm)], ['6', '9'])).
% 0.35/0.55  thf('12', plain,
% 0.35/0.55      (![X5 : $i, X7 : $i, X9 : $i]:
% 0.35/0.55         (((X9) = (k2_xboole_0 @ X7 @ X5))
% 0.35/0.55          | ~ (r2_hidden @ (sk_D @ X9 @ X5 @ X7) @ X5)
% 0.35/0.55          | ~ (r2_hidden @ (sk_D @ X9 @ X5 @ X7) @ X9))),
% 0.35/0.55      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.35/0.55  thf('13', plain,
% 0.35/0.55      ((((sk_B) = (k2_xboole_0 @ sk_A @ sk_B))
% 0.35/0.55        | ~ (r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ sk_B)
% 0.35/0.55        | ((sk_B) = (k2_xboole_0 @ sk_A @ sk_B)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.35/0.55  thf('14', plain,
% 0.35/0.55      ((~ (r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ sk_B)
% 0.35/0.55        | ((sk_B) = (k2_xboole_0 @ sk_A @ sk_B)))),
% 0.35/0.55      inference('simplify', [status(thm)], ['13'])).
% 0.35/0.55  thf('15', plain, (((k2_xboole_0 @ sk_A @ sk_B) != (sk_B))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('16', plain, (~ (r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ sk_B)),
% 0.35/0.55      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.35/0.55  thf('17', plain, (((sk_B) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.35/0.55      inference('sup-', [status(thm)], ['10', '16'])).
% 0.35/0.55  thf('18', plain, (((k2_xboole_0 @ sk_A @ sk_B) != (sk_B))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('19', plain, ($false),
% 0.35/0.55      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 0.35/0.55  
% 0.35/0.55  % SZS output end Refutation
% 0.35/0.55  
% 0.38/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
