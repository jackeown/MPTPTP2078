%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RAiXIFAIP0

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   27 (  34 expanded)
%              Number of leaves         :   10 (  15 expanded)
%              Depth                    :    9
%              Number of atoms          :  137 ( 204 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t8_setfam_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r2_hidden @ A @ B )
          & ( r1_tarski @ A @ C ) )
       => ( r1_tarski @ ( k1_setfam_1 @ B ) @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t8_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ sk_C_1 ) ),
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
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X4 ) @ X5 )
      | ~ ( r2_hidden @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('4',plain,(
    r1_tarski @ ( k1_setfam_1 @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_setfam_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_setfam_1 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    r1_tarski @ sk_A @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_setfam_1 @ sk_B ) ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,
    ( ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ sk_C_1 )
    | ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ ( k1_setfam_1 @ sk_B ) @ sk_C_1 ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    $false ),
    inference(demod,[status(thm)],['0','14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RAiXIFAIP0
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:42:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.44  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.44  % Solved by: fo/fo7.sh
% 0.21/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.44  % done 23 iterations in 0.016s
% 0.21/0.44  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.44  % SZS output start Refutation
% 0.21/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.44  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.44  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.44  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.44  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.44  thf(t8_setfam_1, conjecture,
% 0.21/0.44    (![A:$i,B:$i,C:$i]:
% 0.21/0.44     ( ( ( r2_hidden @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.21/0.44       ( r1_tarski @ ( k1_setfam_1 @ B ) @ C ) ))).
% 0.21/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.44    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.44        ( ( ( r2_hidden @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.21/0.44          ( r1_tarski @ ( k1_setfam_1 @ B ) @ C ) ) )),
% 0.21/0.44    inference('cnf.neg', [status(esa)], [t8_setfam_1])).
% 0.21/0.44  thf('0', plain, (~ (r1_tarski @ (k1_setfam_1 @ sk_B) @ sk_C_1)),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf(d3_tarski, axiom,
% 0.21/0.44    (![A:$i,B:$i]:
% 0.21/0.44     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.44       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.44  thf('1', plain,
% 0.21/0.44      (![X1 : $i, X3 : $i]:
% 0.21/0.44         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.44      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.44  thf('2', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf(t4_setfam_1, axiom,
% 0.21/0.44    (![A:$i,B:$i]:
% 0.21/0.44     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 0.21/0.44  thf('3', plain,
% 0.21/0.44      (![X4 : $i, X5 : $i]:
% 0.21/0.44         ((r1_tarski @ (k1_setfam_1 @ X4) @ X5) | ~ (r2_hidden @ X5 @ X4))),
% 0.21/0.44      inference('cnf', [status(esa)], [t4_setfam_1])).
% 0.21/0.44  thf('4', plain, ((r1_tarski @ (k1_setfam_1 @ sk_B) @ sk_A)),
% 0.21/0.44      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.44  thf('5', plain,
% 0.21/0.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.44         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.44          | (r2_hidden @ X0 @ X2)
% 0.21/0.44          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.44      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.44  thf('6', plain,
% 0.21/0.44      (![X0 : $i]:
% 0.21/0.44         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_setfam_1 @ sk_B)))),
% 0.21/0.44      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.44  thf('7', plain,
% 0.21/0.44      (![X0 : $i]:
% 0.21/0.44         ((r1_tarski @ (k1_setfam_1 @ sk_B) @ X0)
% 0.21/0.44          | (r2_hidden @ (sk_C @ X0 @ (k1_setfam_1 @ sk_B)) @ sk_A))),
% 0.21/0.44      inference('sup-', [status(thm)], ['1', '6'])).
% 0.21/0.44  thf('8', plain, ((r1_tarski @ sk_A @ sk_C_1)),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf('9', plain,
% 0.21/0.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.44         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.44          | (r2_hidden @ X0 @ X2)
% 0.21/0.44          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.44      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.44  thf('10', plain,
% 0.21/0.44      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_1) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.44      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.44  thf('11', plain,
% 0.21/0.44      (![X0 : $i]:
% 0.21/0.44         ((r1_tarski @ (k1_setfam_1 @ sk_B) @ X0)
% 0.21/0.44          | (r2_hidden @ (sk_C @ X0 @ (k1_setfam_1 @ sk_B)) @ sk_C_1))),
% 0.21/0.44      inference('sup-', [status(thm)], ['7', '10'])).
% 0.21/0.44  thf('12', plain,
% 0.21/0.44      (![X1 : $i, X3 : $i]:
% 0.21/0.44         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.44      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.44  thf('13', plain,
% 0.21/0.44      (((r1_tarski @ (k1_setfam_1 @ sk_B) @ sk_C_1)
% 0.21/0.44        | (r1_tarski @ (k1_setfam_1 @ sk_B) @ sk_C_1))),
% 0.21/0.44      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.44  thf('14', plain, ((r1_tarski @ (k1_setfam_1 @ sk_B) @ sk_C_1)),
% 0.21/0.44      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.44  thf('15', plain, ($false), inference('demod', [status(thm)], ['0', '14'])).
% 0.21/0.44  
% 0.21/0.44  % SZS output end Refutation
% 0.21/0.44  
% 0.21/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
