%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tculp1LMZ8

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:39 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   27 (  32 expanded)
%              Number of leaves         :   12 (  15 expanded)
%              Depth                    :    7
%              Number of atoms          :  125 ( 174 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t9_setfam_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_xboole_0 @ ( k1_setfam_1 @ B ) @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r2_hidden @ A @ B )
          & ( r1_xboole_0 @ A @ C ) )
       => ( r1_xboole_0 @ ( k1_setfam_1 @ B ) @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t9_setfam_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k1_setfam_1 @ sk_B ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ C ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_tarski @ X7 @ X9 )
      | ( r1_tarski @ ( k1_setfam_1 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t8_setfam_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ ( k1_setfam_1 @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['5','8'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X5 @ X6 )
      | ( r1_xboole_0 @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k1_setfam_1 @ sk_B ) @ X0 )
      | ~ ( r1_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r1_xboole_0 @ ( k1_setfam_1 @ sk_B ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['1','11'])).

thf('13',plain,(
    $false ),
    inference(demod,[status(thm)],['0','12'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tculp1LMZ8
% 0.14/0.36  % Computer   : n003.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 14:27:42 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.22/0.36  % Number of cores: 8
% 0.22/0.36  % Python version: Python 3.6.8
% 0.22/0.36  % Running in FO mode
% 0.22/0.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.44  % Solved by: fo/fo7.sh
% 0.22/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.44  % done 20 iterations in 0.009s
% 0.22/0.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.44  % SZS output start Refutation
% 0.22/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.44  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.44  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.22/0.44  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.44  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.44  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.44  thf(t9_setfam_1, conjecture,
% 0.22/0.44    (![A:$i,B:$i,C:$i]:
% 0.22/0.44     ( ( ( r2_hidden @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.22/0.44       ( r1_xboole_0 @ ( k1_setfam_1 @ B ) @ C ) ))).
% 0.22/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.44    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.44        ( ( ( r2_hidden @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.22/0.44          ( r1_xboole_0 @ ( k1_setfam_1 @ B ) @ C ) ) )),
% 0.22/0.44    inference('cnf.neg', [status(esa)], [t9_setfam_1])).
% 0.22/0.44  thf('0', plain, (~ (r1_xboole_0 @ (k1_setfam_1 @ sk_B) @ sk_C_1)),
% 0.22/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.44  thf('1', plain, ((r1_xboole_0 @ sk_A @ sk_C_1)),
% 0.22/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.44  thf(d3_tarski, axiom,
% 0.22/0.44    (![A:$i,B:$i]:
% 0.22/0.44     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.44       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.44  thf('2', plain,
% 0.22/0.44      (![X1 : $i, X3 : $i]:
% 0.22/0.44         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.22/0.44      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.44  thf('3', plain,
% 0.22/0.44      (![X1 : $i, X3 : $i]:
% 0.22/0.44         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.22/0.44      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.44  thf('4', plain,
% 0.22/0.44      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.22/0.44      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.44  thf('5', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.22/0.44      inference('simplify', [status(thm)], ['4'])).
% 0.22/0.44  thf('6', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.22/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.44  thf(t8_setfam_1, axiom,
% 0.22/0.44    (![A:$i,B:$i,C:$i]:
% 0.22/0.44     ( ( ( r2_hidden @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.22/0.44       ( r1_tarski @ ( k1_setfam_1 @ B ) @ C ) ))).
% 0.22/0.44  thf('7', plain,
% 0.22/0.44      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.44         (~ (r2_hidden @ X7 @ X8)
% 0.22/0.44          | ~ (r1_tarski @ X7 @ X9)
% 0.22/0.44          | (r1_tarski @ (k1_setfam_1 @ X8) @ X9))),
% 0.22/0.44      inference('cnf', [status(esa)], [t8_setfam_1])).
% 0.22/0.44  thf('8', plain,
% 0.22/0.44      (![X0 : $i]:
% 0.22/0.44         ((r1_tarski @ (k1_setfam_1 @ sk_B) @ X0) | ~ (r1_tarski @ sk_A @ X0))),
% 0.22/0.44      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.44  thf('9', plain, ((r1_tarski @ (k1_setfam_1 @ sk_B) @ sk_A)),
% 0.22/0.44      inference('sup-', [status(thm)], ['5', '8'])).
% 0.22/0.44  thf(t63_xboole_1, axiom,
% 0.22/0.44    (![A:$i,B:$i,C:$i]:
% 0.22/0.44     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.22/0.44       ( r1_xboole_0 @ A @ C ) ))).
% 0.22/0.44  thf('10', plain,
% 0.22/0.44      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.44         (~ (r1_tarski @ X4 @ X5)
% 0.22/0.44          | ~ (r1_xboole_0 @ X5 @ X6)
% 0.22/0.44          | (r1_xboole_0 @ X4 @ X6))),
% 0.22/0.44      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.22/0.44  thf('11', plain,
% 0.22/0.44      (![X0 : $i]:
% 0.22/0.44         ((r1_xboole_0 @ (k1_setfam_1 @ sk_B) @ X0)
% 0.22/0.44          | ~ (r1_xboole_0 @ sk_A @ X0))),
% 0.22/0.44      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.44  thf('12', plain, ((r1_xboole_0 @ (k1_setfam_1 @ sk_B) @ sk_C_1)),
% 0.22/0.44      inference('sup-', [status(thm)], ['1', '11'])).
% 0.22/0.44  thf('13', plain, ($false), inference('demod', [status(thm)], ['0', '12'])).
% 0.22/0.44  
% 0.22/0.44  % SZS output end Refutation
% 0.22/0.44  
% 0.23/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
