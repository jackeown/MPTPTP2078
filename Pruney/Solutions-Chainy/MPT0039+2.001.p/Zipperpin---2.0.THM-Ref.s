%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.M03gbH0YZw

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:58 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   45 (  69 expanded)
%              Number of leaves         :   12 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :  301 ( 552 expanded)
%              Number of equality atoms :   20 (  42 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( r2_hidden @ X6 @ X8 )
      | ( r2_hidden @ X6 @ X9 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('2',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X6 @ ( k4_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf(t32_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = ( k4_xboole_0 @ B @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ A @ B )
          = ( k4_xboole_0 @ B @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t32_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X7 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('6',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('9',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf('12',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['13'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('15',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k4_xboole_0 @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_A )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['7','9'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('23',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('26',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['24','25'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('28',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    sk_A = sk_B ),
    inference('sup+',[status(thm)],['16','28'])).

thf('30',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.M03gbH0YZw
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:32:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.48/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.48/0.68  % Solved by: fo/fo7.sh
% 0.48/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.68  % done 532 iterations in 0.211s
% 0.48/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.48/0.68  % SZS output start Refutation
% 0.48/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.48/0.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.48/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.48/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.48/0.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.48/0.68  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.48/0.68  thf(d3_tarski, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( r1_tarski @ A @ B ) <=>
% 0.48/0.68       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.48/0.68  thf('0', plain,
% 0.48/0.68      (![X3 : $i, X5 : $i]:
% 0.48/0.68         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.48/0.68      inference('cnf', [status(esa)], [d3_tarski])).
% 0.48/0.68  thf(d5_xboole_0, axiom,
% 0.48/0.68    (![A:$i,B:$i,C:$i]:
% 0.48/0.68     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.48/0.68       ( ![D:$i]:
% 0.48/0.68         ( ( r2_hidden @ D @ C ) <=>
% 0.48/0.68           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.48/0.68  thf('1', plain,
% 0.48/0.68      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.48/0.68         (~ (r2_hidden @ X6 @ X7)
% 0.48/0.68          | (r2_hidden @ X6 @ X8)
% 0.48/0.68          | (r2_hidden @ X6 @ X9)
% 0.48/0.68          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.48/0.68      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.48/0.68  thf('2', plain,
% 0.48/0.68      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.48/0.68         ((r2_hidden @ X6 @ (k4_xboole_0 @ X7 @ X8))
% 0.48/0.68          | (r2_hidden @ X6 @ X8)
% 0.48/0.68          | ~ (r2_hidden @ X6 @ X7))),
% 0.48/0.68      inference('simplify', [status(thm)], ['1'])).
% 0.48/0.68  thf('3', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.68         ((r1_tarski @ X0 @ X1)
% 0.48/0.68          | (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 0.48/0.68          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X2)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['0', '2'])).
% 0.48/0.68  thf(t32_xboole_1, conjecture,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( ( k4_xboole_0 @ A @ B ) = ( k4_xboole_0 @ B @ A ) ) =>
% 0.48/0.68       ( ( A ) = ( B ) ) ))).
% 0.48/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.68    (~( ![A:$i,B:$i]:
% 0.48/0.68        ( ( ( k4_xboole_0 @ A @ B ) = ( k4_xboole_0 @ B @ A ) ) =>
% 0.48/0.68          ( ( A ) = ( B ) ) ) )),
% 0.48/0.68    inference('cnf.neg', [status(esa)], [t32_xboole_1])).
% 0.48/0.68  thf('4', plain,
% 0.48/0.68      (((k4_xboole_0 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_B @ sk_A))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('5', plain,
% 0.48/0.68      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.48/0.68         (~ (r2_hidden @ X10 @ X9)
% 0.48/0.68          | (r2_hidden @ X10 @ X7)
% 0.48/0.68          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.48/0.68      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.48/0.68  thf('6', plain,
% 0.48/0.68      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.48/0.68         ((r2_hidden @ X10 @ X7)
% 0.48/0.68          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.48/0.68      inference('simplify', [status(thm)], ['5'])).
% 0.48/0.68  thf('7', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.48/0.68          | (r2_hidden @ X0 @ sk_B))),
% 0.48/0.68      inference('sup-', [status(thm)], ['4', '6'])).
% 0.48/0.68  thf('8', plain,
% 0.48/0.68      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.48/0.68         (~ (r2_hidden @ X10 @ X9)
% 0.48/0.68          | ~ (r2_hidden @ X10 @ X8)
% 0.48/0.68          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.48/0.68      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.48/0.68  thf('9', plain,
% 0.48/0.68      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.48/0.68         (~ (r2_hidden @ X10 @ X8)
% 0.48/0.68          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.48/0.68      inference('simplify', [status(thm)], ['8'])).
% 0.48/0.68  thf('10', plain,
% 0.48/0.68      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.48/0.68      inference('clc', [status(thm)], ['7', '9'])).
% 0.48/0.68  thf('11', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         ((r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B) | (r1_tarski @ sk_A @ X0))),
% 0.48/0.68      inference('sup-', [status(thm)], ['3', '10'])).
% 0.48/0.68  thf('12', plain,
% 0.48/0.68      (![X3 : $i, X5 : $i]:
% 0.48/0.68         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.48/0.68      inference('cnf', [status(esa)], [d3_tarski])).
% 0.48/0.68  thf('13', plain, (((r1_tarski @ sk_A @ sk_B) | (r1_tarski @ sk_A @ sk_B))),
% 0.48/0.68      inference('sup-', [status(thm)], ['11', '12'])).
% 0.48/0.68  thf('14', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.48/0.68      inference('simplify', [status(thm)], ['13'])).
% 0.48/0.68  thf(t28_xboole_1, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.48/0.68  thf('15', plain,
% 0.48/0.68      (![X12 : $i, X13 : $i]:
% 0.48/0.68         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.48/0.68      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.48/0.68  thf('16', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.48/0.68      inference('sup-', [status(thm)], ['14', '15'])).
% 0.48/0.68  thf('17', plain,
% 0.48/0.68      (((k4_xboole_0 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_B @ sk_A))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('18', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.68         ((r1_tarski @ X0 @ X1)
% 0.48/0.68          | (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 0.48/0.68          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X2)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['0', '2'])).
% 0.48/0.68  thf('19', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.48/0.68          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_A)
% 0.48/0.68          | (r1_tarski @ sk_B @ X0))),
% 0.48/0.68      inference('sup+', [status(thm)], ['17', '18'])).
% 0.48/0.68  thf('20', plain,
% 0.48/0.68      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.48/0.68      inference('clc', [status(thm)], ['7', '9'])).
% 0.48/0.68  thf('21', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         ((r1_tarski @ sk_B @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 0.48/0.68      inference('clc', [status(thm)], ['19', '20'])).
% 0.48/0.68  thf('22', plain,
% 0.48/0.68      (![X3 : $i, X5 : $i]:
% 0.48/0.68         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.48/0.68      inference('cnf', [status(esa)], [d3_tarski])).
% 0.48/0.68  thf('23', plain, (((r1_tarski @ sk_B @ sk_A) | (r1_tarski @ sk_B @ sk_A))),
% 0.48/0.68      inference('sup-', [status(thm)], ['21', '22'])).
% 0.48/0.68  thf('24', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.48/0.68      inference('simplify', [status(thm)], ['23'])).
% 0.48/0.68  thf('25', plain,
% 0.48/0.68      (![X12 : $i, X13 : $i]:
% 0.48/0.68         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.48/0.68      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.48/0.68  thf('26', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.48/0.68      inference('sup-', [status(thm)], ['24', '25'])).
% 0.48/0.68  thf(commutativity_k3_xboole_0, axiom,
% 0.48/0.68    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.48/0.68  thf('27', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.48/0.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.48/0.68  thf('28', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.48/0.68      inference('demod', [status(thm)], ['26', '27'])).
% 0.48/0.68  thf('29', plain, (((sk_A) = (sk_B))),
% 0.48/0.68      inference('sup+', [status(thm)], ['16', '28'])).
% 0.48/0.68  thf('30', plain, (((sk_A) != (sk_B))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('31', plain, ($false),
% 0.48/0.68      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.48/0.68  
% 0.48/0.68  % SZS output end Refutation
% 0.48/0.68  
% 0.48/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
