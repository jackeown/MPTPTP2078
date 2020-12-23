%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pTs3F1cYxn

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:21 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   38 (  61 expanded)
%              Number of leaves         :   13 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :  236 ( 534 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t91_mcart_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( ( r2_hidden @ ( k1_mcart_1 @ B ) @ ( k1_relat_1 @ A ) )
            & ( r2_hidden @ ( k2_mcart_1 @ B ) @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( r2_hidden @ B @ A )
           => ( ( r2_hidden @ ( k1_mcart_1 @ B ) @ ( k1_relat_1 @ A ) )
              & ( r2_hidden @ ( k2_mcart_1 @ B ) @ ( k2_relat_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t91_mcart_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_B ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_B ) @ ( k2_relat_1 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k2_mcart_1 @ sk_B ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t23_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( A
          = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14
        = ( k4_tarski @ ( k1_mcart_1 @ X14 ) @ ( k2_mcart_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X15 )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('5',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( sk_B
      = ( k4_tarski @ ( k1_mcart_1 @ sk_B ) @ ( k2_mcart_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( sk_B
    = ( k4_tarski @ ( k1_mcart_1 @ sk_B ) @ ( k2_mcart_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k1_relat_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ X2 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ ( k1_mcart_1 @ sk_B ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf('12',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_mcart_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('13',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_B ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('15',plain,(
    ~ ( r2_hidden @ ( k2_mcart_1 @ sk_B ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['13','14'])).

thf('16',plain,(
    ~ ( r2_hidden @ ( k2_mcart_1 @ sk_B ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','15'])).

thf('17',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( sk_B
    = ( k4_tarski @ ( k1_mcart_1 @ sk_B ) @ ( k2_mcart_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('19',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ( X10
       != ( k2_relat_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('20',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ ( k2_relat_1 @ X9 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ X9 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_B ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_B ) @ ( k2_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','21'])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['16','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pTs3F1cYxn
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:10:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 25 iterations in 0.022s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.48  thf(t91_mcart_1, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( r2_hidden @ B @ A ) =>
% 0.20/0.48           ( ( r2_hidden @ ( k1_mcart_1 @ B ) @ ( k1_relat_1 @ A ) ) & 
% 0.20/0.48             ( r2_hidden @ ( k2_mcart_1 @ B ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( v1_relat_1 @ A ) =>
% 0.20/0.48          ( ![B:$i]:
% 0.20/0.48            ( ( r2_hidden @ B @ A ) =>
% 0.20/0.48              ( ( r2_hidden @ ( k1_mcart_1 @ B ) @ ( k1_relat_1 @ A ) ) & 
% 0.20/0.48                ( r2_hidden @ ( k2_mcart_1 @ B ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t91_mcart_1])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      ((~ (r2_hidden @ (k1_mcart_1 @ sk_B) @ (k1_relat_1 @ sk_A))
% 0.20/0.48        | ~ (r2_hidden @ (k2_mcart_1 @ sk_B) @ (k2_relat_1 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      ((~ (r2_hidden @ (k2_mcart_1 @ sk_B) @ (k2_relat_1 @ sk_A)))
% 0.20/0.48         <= (~ ((r2_hidden @ (k2_mcart_1 @ sk_B) @ (k2_relat_1 @ sk_A))))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('2', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('3', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t23_mcart_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ B ) =>
% 0.20/0.48       ( ( r2_hidden @ A @ B ) =>
% 0.20/0.48         ( ( A ) = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ))).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X14 : $i, X15 : $i]:
% 0.20/0.48         (((X14) = (k4_tarski @ (k1_mcart_1 @ X14) @ (k2_mcart_1 @ X14)))
% 0.20/0.48          | ~ (v1_relat_1 @ X15)
% 0.20/0.48          | ~ (r2_hidden @ X14 @ X15))),
% 0.20/0.48      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      ((~ (v1_relat_1 @ sk_A)
% 0.20/0.48        | ((sk_B) = (k4_tarski @ (k1_mcart_1 @ sk_B) @ (k2_mcart_1 @ sk_B))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.48  thf('6', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (((sk_B) = (k4_tarski @ (k1_mcart_1 @ sk_B) @ (k2_mcart_1 @ sk_B)))),
% 0.20/0.48      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf(d4_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.20/0.48       ( ![C:$i]:
% 0.20/0.48         ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.48           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         (~ (r2_hidden @ (k4_tarski @ X0 @ X1) @ X2)
% 0.20/0.48          | (r2_hidden @ X0 @ X3)
% 0.20/0.48          | ((X3) != (k1_relat_1 @ X2)))),
% 0.20/0.48      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         ((r2_hidden @ X0 @ (k1_relat_1 @ X2))
% 0.20/0.48          | ~ (r2_hidden @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.20/0.48      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (r2_hidden @ sk_B @ X0)
% 0.20/0.48          | (r2_hidden @ (k1_mcart_1 @ sk_B) @ (k1_relat_1 @ X0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['7', '9'])).
% 0.20/0.48  thf('11', plain, ((r2_hidden @ (k1_mcart_1 @ sk_B) @ (k1_relat_1 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '10'])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      ((~ (r2_hidden @ (k1_mcart_1 @ sk_B) @ (k1_relat_1 @ sk_A)))
% 0.20/0.48         <= (~ ((r2_hidden @ (k1_mcart_1 @ sk_B) @ (k1_relat_1 @ sk_A))))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('13', plain, (((r2_hidden @ (k1_mcart_1 @ sk_B) @ (k1_relat_1 @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (~ ((r2_hidden @ (k2_mcart_1 @ sk_B) @ (k2_relat_1 @ sk_A))) | 
% 0.20/0.48       ~ ((r2_hidden @ (k1_mcart_1 @ sk_B) @ (k1_relat_1 @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (~ ((r2_hidden @ (k2_mcart_1 @ sk_B) @ (k2_relat_1 @ sk_A)))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['13', '14'])).
% 0.20/0.48  thf('16', plain, (~ (r2_hidden @ (k2_mcart_1 @ sk_B) @ (k2_relat_1 @ sk_A))),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['1', '15'])).
% 0.20/0.48  thf('17', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (((sk_B) = (k4_tarski @ (k1_mcart_1 @ sk_B) @ (k2_mcart_1 @ sk_B)))),
% 0.20/0.48      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf(d5_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.20/0.48       ( ![C:$i]:
% 0.20/0.48         ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.48           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.48         (~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ X9)
% 0.20/0.48          | (r2_hidden @ X8 @ X10)
% 0.20/0.48          | ((X10) != (k2_relat_1 @ X9)))),
% 0.20/0.48      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.48         ((r2_hidden @ X8 @ (k2_relat_1 @ X9))
% 0.20/0.48          | ~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ X9))),
% 0.20/0.48      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (r2_hidden @ sk_B @ X0)
% 0.20/0.48          | (r2_hidden @ (k2_mcart_1 @ sk_B) @ (k2_relat_1 @ X0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['18', '20'])).
% 0.20/0.48  thf('22', plain, ((r2_hidden @ (k2_mcart_1 @ sk_B) @ (k2_relat_1 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['17', '21'])).
% 0.20/0.48  thf('23', plain, ($false), inference('demod', [status(thm)], ['16', '22'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
