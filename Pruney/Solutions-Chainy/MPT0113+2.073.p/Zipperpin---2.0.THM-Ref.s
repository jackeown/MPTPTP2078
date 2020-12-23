%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IMrTRZUabL

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:38 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   54 (  79 expanded)
%              Number of leaves         :   13 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :  358 ( 656 expanded)
%              Number of equality atoms :    3 (   4 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t106_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
       => ( ( r1_tarski @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t106_xboole_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
   <= ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

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
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('5',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('11',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r1_xboole_0 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('17',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C_2 ) )
      | ( r1_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C_2 ) )
      | ( r1_xboole_0 @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    r1_xboole_0 @ sk_A @ sk_C_2 ),
    inference('sup-',[status(thm)],['15','23'])).

thf('25',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C_2 )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,(
    r1_xboole_0 @ sk_A @ sk_C_2 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('28',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','28'])).

thf('30',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('34',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('37',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['29','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IMrTRZUabL
% 0.14/0.36  % Computer   : n014.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 09:59:37 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.24/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.51  % Solved by: fo/fo7.sh
% 0.24/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.51  % done 63 iterations in 0.034s
% 0.24/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.51  % SZS output start Refutation
% 0.24/0.51  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.24/0.51  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.24/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.24/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.24/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.24/0.51  thf(t106_xboole_1, conjecture,
% 0.24/0.51    (![A:$i,B:$i,C:$i]:
% 0.24/0.51     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.24/0.51       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.24/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.24/0.51        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.24/0.51          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 0.24/0.51    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 0.24/0.51  thf('0', plain,
% 0.24/0.51      ((~ (r1_tarski @ sk_A @ sk_B) | ~ (r1_xboole_0 @ sk_A @ sk_C_2))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('1', plain,
% 0.24/0.51      ((~ (r1_tarski @ sk_A @ sk_B)) <= (~ ((r1_tarski @ sk_A @ sk_B)))),
% 0.24/0.51      inference('split', [status(esa)], ['0'])).
% 0.24/0.51  thf(t3_xboole_0, axiom,
% 0.24/0.51    (![A:$i,B:$i]:
% 0.24/0.51     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.24/0.51            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.24/0.51       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.24/0.51            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.24/0.51  thf('2', plain,
% 0.24/0.51      (![X10 : $i, X11 : $i]:
% 0.24/0.51         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C_1 @ X11 @ X10) @ X11))),
% 0.24/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.24/0.51  thf('3', plain,
% 0.24/0.51      (![X10 : $i, X11 : $i]:
% 0.24/0.51         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C_1 @ X11 @ X10) @ X10))),
% 0.24/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.24/0.51  thf(d5_xboole_0, axiom,
% 0.24/0.51    (![A:$i,B:$i,C:$i]:
% 0.24/0.51     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.24/0.51       ( ![D:$i]:
% 0.24/0.51         ( ( r2_hidden @ D @ C ) <=>
% 0.24/0.51           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.24/0.51  thf('4', plain,
% 0.24/0.51      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.24/0.51         (~ (r2_hidden @ X8 @ X7)
% 0.24/0.51          | ~ (r2_hidden @ X8 @ X6)
% 0.24/0.51          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.24/0.51      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.24/0.51  thf('5', plain,
% 0.24/0.51      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.24/0.51         (~ (r2_hidden @ X8 @ X6)
% 0.24/0.51          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.24/0.51      inference('simplify', [status(thm)], ['4'])).
% 0.24/0.51  thf('6', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.51         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.24/0.51          | ~ (r2_hidden @ (sk_C_1 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.24/0.51      inference('sup-', [status(thm)], ['3', '5'])).
% 0.24/0.51  thf('7', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]:
% 0.24/0.51         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.24/0.51          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.24/0.51      inference('sup-', [status(thm)], ['2', '6'])).
% 0.24/0.51  thf('8', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.24/0.51      inference('simplify', [status(thm)], ['7'])).
% 0.24/0.51  thf('9', plain,
% 0.24/0.51      (![X10 : $i, X11 : $i]:
% 0.24/0.51         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C_1 @ X11 @ X10) @ X10))),
% 0.24/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.24/0.51  thf('10', plain,
% 0.24/0.51      (![X10 : $i, X11 : $i]:
% 0.24/0.51         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C_1 @ X11 @ X10) @ X11))),
% 0.24/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.24/0.51  thf('11', plain,
% 0.24/0.51      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.24/0.51         (~ (r2_hidden @ X12 @ X10)
% 0.24/0.51          | ~ (r2_hidden @ X12 @ X13)
% 0.24/0.51          | ~ (r1_xboole_0 @ X10 @ X13))),
% 0.24/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.24/0.51  thf('12', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.51         ((r1_xboole_0 @ X1 @ X0)
% 0.24/0.51          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.24/0.51          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X2))),
% 0.24/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.24/0.51  thf('13', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]:
% 0.24/0.51         ((r1_xboole_0 @ X0 @ X1)
% 0.24/0.51          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.24/0.51          | (r1_xboole_0 @ X0 @ X1))),
% 0.24/0.51      inference('sup-', [status(thm)], ['9', '12'])).
% 0.24/0.51  thf('14', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]:
% 0.24/0.51         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.24/0.51      inference('simplify', [status(thm)], ['13'])).
% 0.24/0.51  thf('15', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.24/0.51      inference('sup-', [status(thm)], ['8', '14'])).
% 0.24/0.51  thf('16', plain,
% 0.24/0.51      (![X10 : $i, X11 : $i]:
% 0.24/0.51         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C_1 @ X11 @ X10) @ X10))),
% 0.24/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.24/0.51  thf('17', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_2))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf(d3_tarski, axiom,
% 0.24/0.51    (![A:$i,B:$i]:
% 0.24/0.51     ( ( r1_tarski @ A @ B ) <=>
% 0.24/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.24/0.51  thf('18', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.51         (~ (r2_hidden @ X0 @ X1)
% 0.24/0.51          | (r2_hidden @ X0 @ X2)
% 0.24/0.51          | ~ (r1_tarski @ X1 @ X2))),
% 0.24/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.24/0.51  thf('19', plain,
% 0.24/0.51      (![X0 : $i]:
% 0.24/0.51         ((r2_hidden @ X0 @ (k4_xboole_0 @ sk_B @ sk_C_2))
% 0.24/0.51          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.24/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.24/0.51  thf('20', plain,
% 0.24/0.51      (![X0 : $i]:
% 0.24/0.51         ((r1_xboole_0 @ sk_A @ X0)
% 0.24/0.51          | (r2_hidden @ (sk_C_1 @ X0 @ sk_A) @ (k4_xboole_0 @ sk_B @ sk_C_2)))),
% 0.24/0.51      inference('sup-', [status(thm)], ['16', '19'])).
% 0.24/0.51  thf('21', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.51         ((r1_xboole_0 @ X1 @ X0)
% 0.24/0.51          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.24/0.51          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X2))),
% 0.24/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.24/0.51  thf('22', plain,
% 0.24/0.51      (![X0 : $i]:
% 0.24/0.51         ((r1_xboole_0 @ sk_A @ X0)
% 0.24/0.51          | ~ (r1_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C_2))
% 0.24/0.51          | (r1_xboole_0 @ sk_A @ X0))),
% 0.24/0.51      inference('sup-', [status(thm)], ['20', '21'])).
% 0.24/0.51  thf('23', plain,
% 0.24/0.51      (![X0 : $i]:
% 0.24/0.51         (~ (r1_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C_2))
% 0.24/0.51          | (r1_xboole_0 @ sk_A @ X0))),
% 0.24/0.51      inference('simplify', [status(thm)], ['22'])).
% 0.24/0.51  thf('24', plain, ((r1_xboole_0 @ sk_A @ sk_C_2)),
% 0.24/0.51      inference('sup-', [status(thm)], ['15', '23'])).
% 0.24/0.51  thf('25', plain,
% 0.24/0.51      ((~ (r1_xboole_0 @ sk_A @ sk_C_2)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C_2)))),
% 0.24/0.51      inference('split', [status(esa)], ['0'])).
% 0.24/0.51  thf('26', plain, (((r1_xboole_0 @ sk_A @ sk_C_2))),
% 0.24/0.51      inference('sup-', [status(thm)], ['24', '25'])).
% 0.24/0.51  thf('27', plain,
% 0.24/0.51      (~ ((r1_tarski @ sk_A @ sk_B)) | ~ ((r1_xboole_0 @ sk_A @ sk_C_2))),
% 0.24/0.51      inference('split', [status(esa)], ['0'])).
% 0.24/0.51  thf('28', plain, (~ ((r1_tarski @ sk_A @ sk_B))),
% 0.24/0.51      inference('sat_resolution*', [status(thm)], ['26', '27'])).
% 0.24/0.51  thf('29', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.24/0.51      inference('simpl_trail', [status(thm)], ['1', '28'])).
% 0.24/0.51  thf('30', plain,
% 0.24/0.51      (![X1 : $i, X3 : $i]:
% 0.24/0.51         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.24/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.24/0.51  thf('31', plain,
% 0.24/0.51      (![X0 : $i]:
% 0.24/0.51         ((r2_hidden @ X0 @ (k4_xboole_0 @ sk_B @ sk_C_2))
% 0.24/0.51          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.24/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.24/0.51  thf('32', plain,
% 0.24/0.51      (![X0 : $i]:
% 0.24/0.51         ((r1_tarski @ sk_A @ X0)
% 0.24/0.51          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ (k4_xboole_0 @ sk_B @ sk_C_2)))),
% 0.24/0.51      inference('sup-', [status(thm)], ['30', '31'])).
% 0.24/0.51  thf('33', plain,
% 0.24/0.51      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.24/0.51         (~ (r2_hidden @ X8 @ X7)
% 0.24/0.51          | (r2_hidden @ X8 @ X5)
% 0.24/0.51          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.24/0.51      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.24/0.51  thf('34', plain,
% 0.24/0.51      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.24/0.51         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.24/0.51      inference('simplify', [status(thm)], ['33'])).
% 0.24/0.51  thf('35', plain,
% 0.24/0.51      (![X0 : $i]:
% 0.24/0.51         ((r1_tarski @ sk_A @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 0.24/0.51      inference('sup-', [status(thm)], ['32', '34'])).
% 0.24/0.51  thf('36', plain,
% 0.24/0.51      (![X1 : $i, X3 : $i]:
% 0.24/0.51         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.24/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.24/0.51  thf('37', plain, (((r1_tarski @ sk_A @ sk_B) | (r1_tarski @ sk_A @ sk_B))),
% 0.24/0.51      inference('sup-', [status(thm)], ['35', '36'])).
% 0.24/0.51  thf('38', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.24/0.51      inference('simplify', [status(thm)], ['37'])).
% 0.24/0.51  thf('39', plain, ($false), inference('demod', [status(thm)], ['29', '38'])).
% 0.24/0.51  
% 0.24/0.51  % SZS output end Refutation
% 0.24/0.51  
% 0.24/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
