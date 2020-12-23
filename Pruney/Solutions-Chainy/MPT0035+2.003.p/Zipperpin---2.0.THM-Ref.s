%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oZhhQuoG4R

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:55 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   25 (  32 expanded)
%              Number of leaves         :    9 (  13 expanded)
%              Depth                    :    9
%              Number of atoms          :  185 ( 262 expanded)
%              Number of equality atoms :   14 (  21 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf(t28_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ A @ B )
       => ( ( k3_xboole_0 @ A @ B )
          = A ) ) ),
    inference('cnf.neg',[status(esa)],[t28_xboole_1])).

thf('3',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k3_xboole_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D @ sk_A @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('8',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ~ ( r2_hidden @ ( sk_D @ sk_A @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ ( sk_D @ sk_A @ sk_B @ sk_A ) @ sk_A )
    | ( sk_A
      = ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( r2_hidden @ ( sk_D @ sk_A @ sk_B @ sk_A ) @ sk_A )
    | ( sk_A
      = ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ~ ( r2_hidden @ ( sk_D @ sk_A @ sk_B @ sk_A ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('12',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('13',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oZhhQuoG4R
% 0.13/0.33  % Computer   : n025.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 21:06:51 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 119 iterations in 0.040s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.48  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.19/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(d4_xboole_0, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.19/0.48       ( ![D:$i]:
% 0.19/0.48         ( ( r2_hidden @ D @ C ) <=>
% 0.19/0.48           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.19/0.48  thf('0', plain,
% 0.19/0.48      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.19/0.48         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 0.19/0.48          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 0.19/0.48          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.19/0.48      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.19/0.48  thf('1', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.19/0.48          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.19/0.48      inference('eq_fact', [status(thm)], ['0'])).
% 0.19/0.48  thf('2', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.19/0.48          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.19/0.48      inference('eq_fact', [status(thm)], ['0'])).
% 0.19/0.48  thf(t28_xboole_1, conjecture,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i,B:$i]:
% 0.19/0.48        ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t28_xboole_1])).
% 0.19/0.48  thf('3', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(d3_tarski, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( r1_tarski @ A @ B ) <=>
% 0.19/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.19/0.48  thf('4', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X0 @ X1)
% 0.19/0.48          | (r2_hidden @ X0 @ X2)
% 0.19/0.48          | ~ (r1_tarski @ X1 @ X2))),
% 0.19/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.48  thf('5', plain,
% 0.19/0.48      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.48  thf('6', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((sk_A) = (k3_xboole_0 @ sk_A @ X0))
% 0.19/0.48          | (r2_hidden @ (sk_D @ sk_A @ X0 @ sk_A) @ sk_B))),
% 0.19/0.48      inference('sup-', [status(thm)], ['2', '5'])).
% 0.19/0.48  thf('7', plain,
% 0.19/0.48      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.19/0.48         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 0.19/0.48          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 0.19/0.48          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 0.19/0.48          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.19/0.48      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.19/0.48  thf('8', plain,
% 0.19/0.48      ((((sk_A) = (k3_xboole_0 @ sk_A @ sk_B))
% 0.19/0.48        | ~ (r2_hidden @ (sk_D @ sk_A @ sk_B @ sk_A) @ sk_A)
% 0.19/0.48        | ~ (r2_hidden @ (sk_D @ sk_A @ sk_B @ sk_A) @ sk_A)
% 0.19/0.48        | ((sk_A) = (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.48  thf('9', plain,
% 0.19/0.48      ((~ (r2_hidden @ (sk_D @ sk_A @ sk_B @ sk_A) @ sk_A)
% 0.19/0.48        | ((sk_A) = (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['8'])).
% 0.19/0.48  thf('10', plain, (((k3_xboole_0 @ sk_A @ sk_B) != (sk_A))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('11', plain, (~ (r2_hidden @ (sk_D @ sk_A @ sk_B @ sk_A) @ sk_A)),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.19/0.48  thf('12', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.19/0.48      inference('sup-', [status(thm)], ['1', '11'])).
% 0.19/0.48  thf('13', plain, (((k3_xboole_0 @ sk_A @ sk_B) != (sk_A))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('14', plain, ($false),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.34/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
