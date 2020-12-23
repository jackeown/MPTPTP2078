%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.R3KsrD7TdG

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   33 (  53 expanded)
%              Number of leaves         :   12 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :  201 ( 448 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t25_setfam_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_setfam_1 @ C @ ( k2_tarski @ A @ B ) )
     => ! [D: $i] :
          ~ ( ( r2_hidden @ D @ C )
            & ~ ( r1_tarski @ D @ A )
            & ~ ( r1_tarski @ D @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_setfam_1 @ C @ ( k2_tarski @ A @ B ) )
       => ! [D: $i] :
            ~ ( ( r2_hidden @ D @ C )
              & ~ ( r1_tarski @ D @ A )
              & ~ ( r1_tarski @ D @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_D_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_setfam_1 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r2_hidden @ sk_D_2 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
    <=> ! [C: $i] :
          ~ ( ( r2_hidden @ C @ A )
            & ! [D: $i] :
                ~ ( ( r2_hidden @ D @ B )
                  & ( r1_tarski @ C @ D ) ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ ( sk_D_1 @ X6 @ X7 ) )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( r1_setfam_1 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( r1_setfam_1 @ sk_C_1 @ X0 )
      | ( r1_tarski @ sk_D_2 @ ( sk_D_1 @ sk_D_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ sk_D_2 @ ( sk_D_1 @ sk_D_2 @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    r2_hidden @ sk_D_2 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r1_setfam_1 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X6 @ X7 ) @ X7 )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( r1_setfam_1 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ ( sk_D_1 @ sk_D_2 @ ( k2_tarski @ sk_A @ sk_B ) ) @ ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( X4 = X3 )
      | ( X4 = X0 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('12',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( ( sk_D_1 @ sk_D_2 @ ( k2_tarski @ sk_A @ sk_B ) )
      = sk_A )
    | ( ( sk_D_1 @ sk_D_2 @ ( k2_tarski @ sk_A @ sk_B ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    r1_tarski @ sk_D_2 @ ( sk_D_1 @ sk_D_2 @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('15',plain,
    ( ( r1_tarski @ sk_D_2 @ sk_B )
    | ( ( sk_D_1 @ sk_D_2 @ ( k2_tarski @ sk_A @ sk_B ) )
      = sk_A ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ~ ( r1_tarski @ sk_D_2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( sk_D_1 @ sk_D_2 @ ( k2_tarski @ sk_A @ sk_B ) )
    = sk_A ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    r1_tarski @ sk_D_2 @ sk_A ),
    inference(demod,[status(thm)],['5','17'])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['0','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.R3KsrD7TdG
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:44:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 31 iterations in 0.021s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.47  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.21/0.47  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.21/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.47  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(t25_setfam_1, conjecture,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( r1_setfam_1 @ C @ ( k2_tarski @ A @ B ) ) =>
% 0.21/0.47       ( ![D:$i]:
% 0.21/0.47         ( ~( ( r2_hidden @ D @ C ) & ( ~( r1_tarski @ D @ A ) ) & 
% 0.21/0.47              ( ~( r1_tarski @ D @ B ) ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.47        ( ( r1_setfam_1 @ C @ ( k2_tarski @ A @ B ) ) =>
% 0.21/0.47          ( ![D:$i]:
% 0.21/0.47            ( ~( ( r2_hidden @ D @ C ) & ( ~( r1_tarski @ D @ A ) ) & 
% 0.21/0.47                 ( ~( r1_tarski @ D @ B ) ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t25_setfam_1])).
% 0.21/0.47  thf('0', plain, (~ (r1_tarski @ sk_D_2 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('1', plain, ((r1_setfam_1 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('2', plain, ((r2_hidden @ sk_D_2 @ sk_C_1)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(d2_setfam_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( r1_setfam_1 @ A @ B ) <=>
% 0.21/0.47       ( ![C:$i]:
% 0.21/0.47         ( ~( ( r2_hidden @ C @ A ) & 
% 0.21/0.47              ( ![D:$i]: ( ~( ( r2_hidden @ D @ B ) & ( r1_tarski @ C @ D ) ) ) ) ) ) ) ))).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.47         ((r1_tarski @ X6 @ (sk_D_1 @ X6 @ X7))
% 0.21/0.47          | ~ (r2_hidden @ X6 @ X8)
% 0.21/0.47          | ~ (r1_setfam_1 @ X8 @ X7))),
% 0.21/0.47      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (r1_setfam_1 @ sk_C_1 @ X0)
% 0.21/0.47          | (r1_tarski @ sk_D_2 @ (sk_D_1 @ sk_D_2 @ X0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      ((r1_tarski @ sk_D_2 @ (sk_D_1 @ sk_D_2 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '4'])).
% 0.21/0.47  thf('6', plain, ((r2_hidden @ sk_D_2 @ sk_C_1)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('7', plain, ((r1_setfam_1 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.47         ((r2_hidden @ (sk_D_1 @ X6 @ X7) @ X7)
% 0.21/0.47          | ~ (r2_hidden @ X6 @ X8)
% 0.21/0.47          | ~ (r1_setfam_1 @ X8 @ X7))),
% 0.21/0.47      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X0 @ sk_C_1)
% 0.21/0.47          | (r2_hidden @ (sk_D_1 @ X0 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.21/0.47             (k2_tarski @ sk_A @ sk_B)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      ((r2_hidden @ (sk_D_1 @ sk_D_2 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.21/0.47        (k2_tarski @ sk_A @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['6', '9'])).
% 0.21/0.47  thf(d2_tarski, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.21/0.47       ( ![D:$i]:
% 0.21/0.47         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X0 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X4 @ X2)
% 0.21/0.47          | ((X4) = (X3))
% 0.21/0.47          | ((X4) = (X0))
% 0.21/0.47          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.21/0.47      inference('cnf', [status(esa)], [d2_tarski])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X0 : $i, X3 : $i, X4 : $i]:
% 0.21/0.47         (((X4) = (X0))
% 0.21/0.47          | ((X4) = (X3))
% 0.21/0.47          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 0.21/0.47      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      ((((sk_D_1 @ sk_D_2 @ (k2_tarski @ sk_A @ sk_B)) = (sk_A))
% 0.21/0.47        | ((sk_D_1 @ sk_D_2 @ (k2_tarski @ sk_A @ sk_B)) = (sk_B)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['10', '12'])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      ((r1_tarski @ sk_D_2 @ (sk_D_1 @ sk_D_2 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '4'])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      (((r1_tarski @ sk_D_2 @ sk_B)
% 0.21/0.47        | ((sk_D_1 @ sk_D_2 @ (k2_tarski @ sk_A @ sk_B)) = (sk_A)))),
% 0.21/0.47      inference('sup+', [status(thm)], ['13', '14'])).
% 0.21/0.47  thf('16', plain, (~ (r1_tarski @ sk_D_2 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('17', plain, (((sk_D_1 @ sk_D_2 @ (k2_tarski @ sk_A @ sk_B)) = (sk_A))),
% 0.21/0.47      inference('clc', [status(thm)], ['15', '16'])).
% 0.21/0.47  thf('18', plain, ((r1_tarski @ sk_D_2 @ sk_A)),
% 0.21/0.47      inference('demod', [status(thm)], ['5', '17'])).
% 0.21/0.47  thf('19', plain, ($false), inference('demod', [status(thm)], ['0', '18'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
