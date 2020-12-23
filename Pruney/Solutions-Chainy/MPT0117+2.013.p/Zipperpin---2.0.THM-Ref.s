%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jR9syjuNGd

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:48 EST 2020

% Result     : Theorem 17.57s
% Output     : Refutation 17.57s
% Verified   : 
% Statistics : Number of formulae       :   37 (  54 expanded)
%              Number of leaves         :   15 (  22 expanded)
%              Depth                    :   11
%              Number of atoms          :  231 ( 396 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ X10 @ X11 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ ( k4_xboole_0 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('2',plain,(
    r1_tarski @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('5',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_C_1 @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','11'])).

thf('13',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('16',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_tarski @ X17 @ X16 )
      | ( r1_tarski @ ( k2_xboole_0 @ X15 @ X17 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ X1 ) @ sk_B )
      | ~ ( r1_tarski @ X1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ X1 ) @ ( k4_xboole_0 @ sk_C_1 @ X0 ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference('sup+',[status(thm)],['1','18'])).

thf('20',plain,(
    $false ),
    inference(demod,[status(thm)],['0','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jR9syjuNGd
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:20:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 17.57/17.79  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 17.57/17.79  % Solved by: fo/fo7.sh
% 17.57/17.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 17.57/17.79  % done 3353 iterations in 17.334s
% 17.57/17.79  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 17.57/17.79  % SZS output start Refutation
% 17.57/17.79  thf(sk_B_type, type, sk_B: $i).
% 17.57/17.79  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 17.57/17.79  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 17.57/17.79  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 17.57/17.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 17.57/17.79  thf(sk_A_type, type, sk_A: $i).
% 17.57/17.79  thf(sk_C_1_type, type, sk_C_1: $i).
% 17.57/17.79  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 17.57/17.79  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 17.57/17.79  thf(t110_xboole_1, conjecture,
% 17.57/17.79    (![A:$i,B:$i,C:$i]:
% 17.57/17.79     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 17.57/17.79       ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 17.57/17.79  thf(zf_stmt_0, negated_conjecture,
% 17.57/17.79    (~( ![A:$i,B:$i,C:$i]:
% 17.57/17.79        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 17.57/17.79          ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )),
% 17.57/17.79    inference('cnf.neg', [status(esa)], [t110_xboole_1])).
% 17.57/17.79  thf('0', plain, (~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 17.57/17.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.57/17.79  thf(d6_xboole_0, axiom,
% 17.57/17.79    (![A:$i,B:$i]:
% 17.57/17.79     ( ( k5_xboole_0 @ A @ B ) =
% 17.57/17.79       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 17.57/17.79  thf('1', plain,
% 17.57/17.79      (![X10 : $i, X11 : $i]:
% 17.57/17.79         ((k5_xboole_0 @ X10 @ X11)
% 17.57/17.79           = (k2_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ 
% 17.57/17.79              (k4_xboole_0 @ X11 @ X10)))),
% 17.57/17.79      inference('cnf', [status(esa)], [d6_xboole_0])).
% 17.57/17.79  thf('2', plain, ((r1_tarski @ sk_C_1 @ sk_B)),
% 17.57/17.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.57/17.79  thf(d3_tarski, axiom,
% 17.57/17.79    (![A:$i,B:$i]:
% 17.57/17.79     ( ( r1_tarski @ A @ B ) <=>
% 17.57/17.79       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 17.57/17.79  thf('3', plain,
% 17.57/17.79      (![X1 : $i, X3 : $i]:
% 17.57/17.79         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 17.57/17.79      inference('cnf', [status(esa)], [d3_tarski])).
% 17.57/17.79  thf(d5_xboole_0, axiom,
% 17.57/17.79    (![A:$i,B:$i,C:$i]:
% 17.57/17.79     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 17.57/17.79       ( ![D:$i]:
% 17.57/17.79         ( ( r2_hidden @ D @ C ) <=>
% 17.57/17.79           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 17.57/17.79  thf('4', plain,
% 17.57/17.79      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 17.57/17.79         (~ (r2_hidden @ X8 @ X7)
% 17.57/17.79          | (r2_hidden @ X8 @ X5)
% 17.57/17.79          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 17.57/17.79      inference('cnf', [status(esa)], [d5_xboole_0])).
% 17.57/17.79  thf('5', plain,
% 17.57/17.79      (![X5 : $i, X6 : $i, X8 : $i]:
% 17.57/17.79         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 17.57/17.79      inference('simplify', [status(thm)], ['4'])).
% 17.57/17.79  thf('6', plain,
% 17.57/17.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.57/17.79         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 17.57/17.79          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 17.57/17.79      inference('sup-', [status(thm)], ['3', '5'])).
% 17.57/17.79  thf('7', plain,
% 17.57/17.79      (![X1 : $i, X3 : $i]:
% 17.57/17.79         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 17.57/17.79      inference('cnf', [status(esa)], [d3_tarski])).
% 17.57/17.79  thf('8', plain,
% 17.57/17.79      (![X0 : $i, X1 : $i]:
% 17.57/17.79         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 17.57/17.79          | (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 17.57/17.79      inference('sup-', [status(thm)], ['6', '7'])).
% 17.57/17.79  thf('9', plain,
% 17.57/17.79      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 17.57/17.79      inference('simplify', [status(thm)], ['8'])).
% 17.57/17.79  thf(t1_xboole_1, axiom,
% 17.57/17.79    (![A:$i,B:$i,C:$i]:
% 17.57/17.79     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 17.57/17.79       ( r1_tarski @ A @ C ) ))).
% 17.57/17.79  thf('10', plain,
% 17.57/17.79      (![X12 : $i, X13 : $i, X14 : $i]:
% 17.57/17.79         (~ (r1_tarski @ X12 @ X13)
% 17.57/17.79          | ~ (r1_tarski @ X13 @ X14)
% 17.57/17.79          | (r1_tarski @ X12 @ X14))),
% 17.57/17.79      inference('cnf', [status(esa)], [t1_xboole_1])).
% 17.57/17.79  thf('11', plain,
% 17.57/17.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.57/17.79         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 17.57/17.79      inference('sup-', [status(thm)], ['9', '10'])).
% 17.57/17.79  thf('12', plain,
% 17.57/17.79      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_C_1 @ X0) @ sk_B)),
% 17.57/17.79      inference('sup-', [status(thm)], ['2', '11'])).
% 17.57/17.79  thf('13', plain, ((r1_tarski @ sk_A @ sk_B)),
% 17.57/17.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.57/17.79  thf('14', plain,
% 17.57/17.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.57/17.79         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 17.57/17.79      inference('sup-', [status(thm)], ['9', '10'])).
% 17.57/17.79  thf('15', plain,
% 17.57/17.79      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_A @ X0) @ sk_B)),
% 17.57/17.79      inference('sup-', [status(thm)], ['13', '14'])).
% 17.57/17.79  thf(t8_xboole_1, axiom,
% 17.57/17.79    (![A:$i,B:$i,C:$i]:
% 17.57/17.79     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 17.57/17.79       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 17.57/17.79  thf('16', plain,
% 17.57/17.79      (![X15 : $i, X16 : $i, X17 : $i]:
% 17.57/17.79         (~ (r1_tarski @ X15 @ X16)
% 17.57/17.79          | ~ (r1_tarski @ X17 @ X16)
% 17.57/17.79          | (r1_tarski @ (k2_xboole_0 @ X15 @ X17) @ X16))),
% 17.57/17.79      inference('cnf', [status(esa)], [t8_xboole_1])).
% 17.57/17.79  thf('17', plain,
% 17.57/17.79      (![X0 : $i, X1 : $i]:
% 17.57/17.79         ((r1_tarski @ (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ X1) @ sk_B)
% 17.57/17.79          | ~ (r1_tarski @ X1 @ sk_B))),
% 17.57/17.79      inference('sup-', [status(thm)], ['15', '16'])).
% 17.57/17.79  thf('18', plain,
% 17.57/17.79      (![X0 : $i, X1 : $i]:
% 17.57/17.79         (r1_tarski @ 
% 17.57/17.79          (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ X1) @ 
% 17.57/17.79           (k4_xboole_0 @ sk_C_1 @ X0)) @ 
% 17.57/17.79          sk_B)),
% 17.57/17.79      inference('sup-', [status(thm)], ['12', '17'])).
% 17.57/17.79  thf('19', plain, ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 17.57/17.79      inference('sup+', [status(thm)], ['1', '18'])).
% 17.57/17.79  thf('20', plain, ($false), inference('demod', [status(thm)], ['0', '19'])).
% 17.57/17.79  
% 17.57/17.79  % SZS output end Refutation
% 17.57/17.79  
% 17.67/17.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
