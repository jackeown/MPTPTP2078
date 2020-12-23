%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BQSBOHas1k

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:00 EST 2020

% Result     : Theorem 0.71s
% Output     : Refutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 126 expanded)
%              Number of leaves         :   13 (  37 expanded)
%              Depth                    :   18
%              Number of atoms          :  466 (1062 expanded)
%              Number of equality atoms :   34 (  89 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(t37_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ A @ B )
          = k1_xboole_0 )
      <=> ( r1_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t37_xboole_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B_2 )
    | ( ( k4_xboole_0 @ sk_A @ sk_B_2 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B_2 )
   <= ~ ( r1_tarski @ sk_A @ sk_B_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B_2 )
    | ( ( k4_xboole_0 @ sk_A @ sk_B_2 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('3',plain,(
    ! [X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( r2_hidden @ X11 @ X8 )
      | ( X10
       != ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('5',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ( r2_hidden @ X11 @ X8 )
      | ~ ( r2_hidden @ X11 @ ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('8',plain,
    ( ( r1_tarski @ sk_A @ sk_B_2 )
    | ( ( k4_xboole_0 @ sk_A @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r1_tarski @ sk_A @ sk_B_2 )
   <= ( r1_tarski @ sk_A @ sk_B_2 ) ),
    inference(split,[status(esa)],['8'])).

thf(t34_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ( r1_tarski @ ( k4_xboole_0 @ X16 @ X15 ) @ ( k4_xboole_0 @ X16 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('11',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_B_2 ) @ ( k4_xboole_0 @ X0 @ sk_A ) )
   <= ( r1_tarski @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ sk_A ) )
        | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ sk_B_2 ) ) )
   <= ( r1_tarski @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ X0 @ sk_B_2 )
          = k1_xboole_0 )
        | ( r2_hidden @ ( sk_B_1 @ ( k4_xboole_0 @ X0 @ sk_B_2 ) ) @ ( k4_xboole_0 @ X0 @ sk_A ) ) )
   <= ( r1_tarski @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf('15',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ~ ( r2_hidden @ X11 @ X9 )
      | ( X10
       != ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('16',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ X0 @ sk_B_2 )
          = k1_xboole_0 )
        | ~ ( r2_hidden @ ( sk_B_1 @ ( k4_xboole_0 @ X0 @ sk_B_2 ) ) @ sk_A ) )
   <= ( r1_tarski @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,
    ( ( ( ( k4_xboole_0 @ sk_A @ sk_B_2 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ sk_A @ sk_B_2 )
        = k1_xboole_0 ) )
   <= ( r1_tarski @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf('19',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
   <= ( r1_tarski @ sk_A @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B_2 )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B_2 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('21',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ sk_B_2 )
       != k1_xboole_0 )
      & ( r1_tarski @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
    | ~ ( r1_tarski @ sk_A @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B_2 ) ),
    inference('sat_resolution*',[status(thm)],['2','22'])).

thf('24',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B_2 ) ),
    inference(simpl_trail,[status(thm)],['1','23'])).

thf('25',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('26',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B_2 ) ),
    inference(split,[status(esa)],['8'])).

thf('27',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_2 )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','22','26'])).

thf('28',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_2 )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('30',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( r2_hidden @ X7 @ X9 )
      | ( r2_hidden @ X7 @ X10 )
      | ( X10
       != ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('31',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X7 @ ( k4_xboole_0 @ X8 @ X9 ) )
      | ( r2_hidden @ X7 @ X9 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B_2 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('35',plain,(
    ! [X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('36',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['33','42'])).

thf('44',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,
    ( ( r1_tarski @ sk_A @ sk_B_2 )
    | ( r1_tarski @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    r1_tarski @ sk_A @ sk_B_2 ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['24','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BQSBOHas1k
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:33:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.71/0.89  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.71/0.89  % Solved by: fo/fo7.sh
% 0.71/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.71/0.89  % done 901 iterations in 0.438s
% 0.71/0.89  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.71/0.89  % SZS output start Refutation
% 0.71/0.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.71/0.89  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.71/0.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.71/0.89  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.71/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.71/0.89  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.71/0.89  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.71/0.89  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.71/0.89  thf(t37_xboole_1, conjecture,
% 0.71/0.89    (![A:$i,B:$i]:
% 0.71/0.89     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.71/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.71/0.89    (~( ![A:$i,B:$i]:
% 0.71/0.89        ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.71/0.89          ( r1_tarski @ A @ B ) ) )),
% 0.71/0.89    inference('cnf.neg', [status(esa)], [t37_xboole_1])).
% 0.71/0.89  thf('0', plain,
% 0.71/0.89      ((~ (r1_tarski @ sk_A @ sk_B_2)
% 0.71/0.89        | ((k4_xboole_0 @ sk_A @ sk_B_2) != (k1_xboole_0)))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('1', plain,
% 0.71/0.89      ((~ (r1_tarski @ sk_A @ sk_B_2)) <= (~ ((r1_tarski @ sk_A @ sk_B_2)))),
% 0.71/0.89      inference('split', [status(esa)], ['0'])).
% 0.71/0.89  thf('2', plain,
% 0.71/0.89      (~ ((r1_tarski @ sk_A @ sk_B_2)) | 
% 0.71/0.89       ~ (((k4_xboole_0 @ sk_A @ sk_B_2) = (k1_xboole_0)))),
% 0.71/0.89      inference('split', [status(esa)], ['0'])).
% 0.71/0.89  thf(t7_xboole_0, axiom,
% 0.71/0.89    (![A:$i]:
% 0.71/0.89     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.71/0.89          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.71/0.89  thf('3', plain,
% 0.71/0.89      (![X13 : $i]:
% 0.71/0.89         (((X13) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X13) @ X13))),
% 0.71/0.89      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.71/0.89  thf(d5_xboole_0, axiom,
% 0.71/0.89    (![A:$i,B:$i,C:$i]:
% 0.71/0.89     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.71/0.89       ( ![D:$i]:
% 0.71/0.89         ( ( r2_hidden @ D @ C ) <=>
% 0.71/0.89           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.71/0.89  thf('4', plain,
% 0.71/0.89      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.71/0.89         (~ (r2_hidden @ X11 @ X10)
% 0.71/0.89          | (r2_hidden @ X11 @ X8)
% 0.71/0.89          | ((X10) != (k4_xboole_0 @ X8 @ X9)))),
% 0.71/0.89      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.71/0.89  thf('5', plain,
% 0.71/0.89      (![X8 : $i, X9 : $i, X11 : $i]:
% 0.71/0.89         ((r2_hidden @ X11 @ X8)
% 0.71/0.89          | ~ (r2_hidden @ X11 @ (k4_xboole_0 @ X8 @ X9)))),
% 0.71/0.89      inference('simplify', [status(thm)], ['4'])).
% 0.71/0.89  thf('6', plain,
% 0.71/0.89      (![X0 : $i, X1 : $i]:
% 0.71/0.89         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.71/0.89          | (r2_hidden @ (sk_B_1 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.71/0.89      inference('sup-', [status(thm)], ['3', '5'])).
% 0.71/0.89  thf('7', plain,
% 0.71/0.89      (![X13 : $i]:
% 0.71/0.89         (((X13) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X13) @ X13))),
% 0.71/0.89      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.71/0.89  thf('8', plain,
% 0.71/0.89      (((r1_tarski @ sk_A @ sk_B_2)
% 0.71/0.89        | ((k4_xboole_0 @ sk_A @ sk_B_2) = (k1_xboole_0)))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('9', plain,
% 0.71/0.89      (((r1_tarski @ sk_A @ sk_B_2)) <= (((r1_tarski @ sk_A @ sk_B_2)))),
% 0.71/0.89      inference('split', [status(esa)], ['8'])).
% 0.71/0.89  thf(t34_xboole_1, axiom,
% 0.71/0.89    (![A:$i,B:$i,C:$i]:
% 0.71/0.89     ( ( r1_tarski @ A @ B ) =>
% 0.71/0.89       ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ))).
% 0.71/0.89  thf('10', plain,
% 0.71/0.89      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.71/0.89         (~ (r1_tarski @ X14 @ X15)
% 0.71/0.89          | (r1_tarski @ (k4_xboole_0 @ X16 @ X15) @ (k4_xboole_0 @ X16 @ X14)))),
% 0.71/0.89      inference('cnf', [status(esa)], [t34_xboole_1])).
% 0.71/0.89  thf('11', plain,
% 0.71/0.89      ((![X0 : $i]:
% 0.71/0.89          (r1_tarski @ (k4_xboole_0 @ X0 @ sk_B_2) @ (k4_xboole_0 @ X0 @ sk_A)))
% 0.71/0.89         <= (((r1_tarski @ sk_A @ sk_B_2)))),
% 0.71/0.89      inference('sup-', [status(thm)], ['9', '10'])).
% 0.71/0.89  thf(d3_tarski, axiom,
% 0.71/0.89    (![A:$i,B:$i]:
% 0.71/0.89     ( ( r1_tarski @ A @ B ) <=>
% 0.71/0.89       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.71/0.89  thf('12', plain,
% 0.71/0.89      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.71/0.89         (~ (r2_hidden @ X3 @ X4)
% 0.71/0.89          | (r2_hidden @ X3 @ X5)
% 0.71/0.89          | ~ (r1_tarski @ X4 @ X5))),
% 0.71/0.89      inference('cnf', [status(esa)], [d3_tarski])).
% 0.71/0.89  thf('13', plain,
% 0.71/0.89      ((![X0 : $i, X1 : $i]:
% 0.71/0.89          ((r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ sk_A))
% 0.71/0.89           | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ sk_B_2))))
% 0.71/0.89         <= (((r1_tarski @ sk_A @ sk_B_2)))),
% 0.71/0.89      inference('sup-', [status(thm)], ['11', '12'])).
% 0.71/0.89  thf('14', plain,
% 0.71/0.89      ((![X0 : $i]:
% 0.71/0.89          (((k4_xboole_0 @ X0 @ sk_B_2) = (k1_xboole_0))
% 0.71/0.89           | (r2_hidden @ (sk_B_1 @ (k4_xboole_0 @ X0 @ sk_B_2)) @ 
% 0.71/0.89              (k4_xboole_0 @ X0 @ sk_A))))
% 0.71/0.89         <= (((r1_tarski @ sk_A @ sk_B_2)))),
% 0.71/0.89      inference('sup-', [status(thm)], ['7', '13'])).
% 0.71/0.89  thf('15', plain,
% 0.71/0.89      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.71/0.89         (~ (r2_hidden @ X11 @ X10)
% 0.71/0.89          | ~ (r2_hidden @ X11 @ X9)
% 0.71/0.89          | ((X10) != (k4_xboole_0 @ X8 @ X9)))),
% 0.71/0.89      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.71/0.89  thf('16', plain,
% 0.71/0.89      (![X8 : $i, X9 : $i, X11 : $i]:
% 0.71/0.89         (~ (r2_hidden @ X11 @ X9)
% 0.71/0.89          | ~ (r2_hidden @ X11 @ (k4_xboole_0 @ X8 @ X9)))),
% 0.71/0.89      inference('simplify', [status(thm)], ['15'])).
% 0.71/0.89  thf('17', plain,
% 0.71/0.89      ((![X0 : $i]:
% 0.71/0.89          (((k4_xboole_0 @ X0 @ sk_B_2) = (k1_xboole_0))
% 0.71/0.89           | ~ (r2_hidden @ (sk_B_1 @ (k4_xboole_0 @ X0 @ sk_B_2)) @ sk_A)))
% 0.71/0.89         <= (((r1_tarski @ sk_A @ sk_B_2)))),
% 0.71/0.89      inference('sup-', [status(thm)], ['14', '16'])).
% 0.71/0.89  thf('18', plain,
% 0.71/0.89      (((((k4_xboole_0 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 0.71/0.89         | ((k4_xboole_0 @ sk_A @ sk_B_2) = (k1_xboole_0))))
% 0.71/0.89         <= (((r1_tarski @ sk_A @ sk_B_2)))),
% 0.71/0.89      inference('sup-', [status(thm)], ['6', '17'])).
% 0.71/0.89  thf('19', plain,
% 0.71/0.89      ((((k4_xboole_0 @ sk_A @ sk_B_2) = (k1_xboole_0)))
% 0.71/0.89         <= (((r1_tarski @ sk_A @ sk_B_2)))),
% 0.71/0.89      inference('simplify', [status(thm)], ['18'])).
% 0.71/0.89  thf('20', plain,
% 0.71/0.89      ((((k4_xboole_0 @ sk_A @ sk_B_2) != (k1_xboole_0)))
% 0.71/0.89         <= (~ (((k4_xboole_0 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.71/0.89      inference('split', [status(esa)], ['0'])).
% 0.71/0.89  thf('21', plain,
% 0.71/0.89      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.71/0.89         <= (~ (((k4_xboole_0 @ sk_A @ sk_B_2) = (k1_xboole_0))) & 
% 0.71/0.89             ((r1_tarski @ sk_A @ sk_B_2)))),
% 0.71/0.89      inference('sup-', [status(thm)], ['19', '20'])).
% 0.71/0.89  thf('22', plain,
% 0.71/0.89      ((((k4_xboole_0 @ sk_A @ sk_B_2) = (k1_xboole_0))) | 
% 0.71/0.89       ~ ((r1_tarski @ sk_A @ sk_B_2))),
% 0.71/0.89      inference('simplify', [status(thm)], ['21'])).
% 0.71/0.89  thf('23', plain, (~ ((r1_tarski @ sk_A @ sk_B_2))),
% 0.71/0.89      inference('sat_resolution*', [status(thm)], ['2', '22'])).
% 0.71/0.89  thf('24', plain, (~ (r1_tarski @ sk_A @ sk_B_2)),
% 0.71/0.89      inference('simpl_trail', [status(thm)], ['1', '23'])).
% 0.71/0.89  thf('25', plain,
% 0.71/0.89      ((((k4_xboole_0 @ sk_A @ sk_B_2) = (k1_xboole_0)))
% 0.71/0.89         <= ((((k4_xboole_0 @ sk_A @ sk_B_2) = (k1_xboole_0))))),
% 0.71/0.89      inference('split', [status(esa)], ['8'])).
% 0.71/0.89  thf('26', plain,
% 0.71/0.89      ((((k4_xboole_0 @ sk_A @ sk_B_2) = (k1_xboole_0))) | 
% 0.71/0.89       ((r1_tarski @ sk_A @ sk_B_2))),
% 0.71/0.89      inference('split', [status(esa)], ['8'])).
% 0.71/0.89  thf('27', plain, ((((k4_xboole_0 @ sk_A @ sk_B_2) = (k1_xboole_0)))),
% 0.71/0.89      inference('sat_resolution*', [status(thm)], ['2', '22', '26'])).
% 0.71/0.89  thf('28', plain, (((k4_xboole_0 @ sk_A @ sk_B_2) = (k1_xboole_0))),
% 0.71/0.89      inference('simpl_trail', [status(thm)], ['25', '27'])).
% 0.71/0.89  thf('29', plain,
% 0.71/0.89      (![X4 : $i, X6 : $i]:
% 0.71/0.89         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.71/0.89      inference('cnf', [status(esa)], [d3_tarski])).
% 0.71/0.89  thf('30', plain,
% 0.71/0.89      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.71/0.89         (~ (r2_hidden @ X7 @ X8)
% 0.71/0.89          | (r2_hidden @ X7 @ X9)
% 0.71/0.89          | (r2_hidden @ X7 @ X10)
% 0.71/0.89          | ((X10) != (k4_xboole_0 @ X8 @ X9)))),
% 0.71/0.89      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.71/0.89  thf('31', plain,
% 0.71/0.89      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.71/0.89         ((r2_hidden @ X7 @ (k4_xboole_0 @ X8 @ X9))
% 0.71/0.89          | (r2_hidden @ X7 @ X9)
% 0.71/0.89          | ~ (r2_hidden @ X7 @ X8))),
% 0.71/0.89      inference('simplify', [status(thm)], ['30'])).
% 0.71/0.89  thf('32', plain,
% 0.71/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.89         ((r1_tarski @ X0 @ X1)
% 0.71/0.89          | (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 0.71/0.89          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X2)))),
% 0.71/0.89      inference('sup-', [status(thm)], ['29', '31'])).
% 0.71/0.89  thf('33', plain,
% 0.71/0.89      (![X0 : $i]:
% 0.71/0.89         ((r2_hidden @ (sk_C @ X0 @ sk_A) @ k1_xboole_0)
% 0.71/0.89          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B_2)
% 0.71/0.89          | (r1_tarski @ sk_A @ X0))),
% 0.71/0.89      inference('sup+', [status(thm)], ['28', '32'])).
% 0.71/0.89  thf('34', plain,
% 0.71/0.89      (![X0 : $i, X1 : $i]:
% 0.71/0.89         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.71/0.89          | (r2_hidden @ (sk_B_1 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.71/0.89      inference('sup-', [status(thm)], ['3', '5'])).
% 0.71/0.89  thf('35', plain,
% 0.71/0.89      (![X13 : $i]:
% 0.71/0.89         (((X13) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X13) @ X13))),
% 0.71/0.89      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.71/0.89  thf('36', plain,
% 0.71/0.89      (![X8 : $i, X9 : $i, X11 : $i]:
% 0.71/0.89         (~ (r2_hidden @ X11 @ X9)
% 0.71/0.89          | ~ (r2_hidden @ X11 @ (k4_xboole_0 @ X8 @ X9)))),
% 0.71/0.89      inference('simplify', [status(thm)], ['15'])).
% 0.71/0.89  thf('37', plain,
% 0.71/0.89      (![X0 : $i, X1 : $i]:
% 0.71/0.89         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.71/0.89          | ~ (r2_hidden @ (sk_B_1 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.71/0.89      inference('sup-', [status(thm)], ['35', '36'])).
% 0.71/0.89  thf('38', plain,
% 0.71/0.89      (![X0 : $i]:
% 0.71/0.89         (((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))
% 0.71/0.89          | ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0)))),
% 0.71/0.89      inference('sup-', [status(thm)], ['34', '37'])).
% 0.71/0.89  thf('39', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.71/0.89      inference('simplify', [status(thm)], ['38'])).
% 0.71/0.89  thf('40', plain,
% 0.71/0.89      (![X8 : $i, X9 : $i, X11 : $i]:
% 0.71/0.89         (~ (r2_hidden @ X11 @ X9)
% 0.71/0.89          | ~ (r2_hidden @ X11 @ (k4_xboole_0 @ X8 @ X9)))),
% 0.71/0.89      inference('simplify', [status(thm)], ['15'])).
% 0.71/0.89  thf('41', plain,
% 0.71/0.89      (![X0 : $i, X1 : $i]:
% 0.71/0.89         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.71/0.89      inference('sup-', [status(thm)], ['39', '40'])).
% 0.71/0.89  thf('42', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.71/0.89      inference('condensation', [status(thm)], ['41'])).
% 0.71/0.89  thf('43', plain,
% 0.71/0.89      (![X0 : $i]:
% 0.71/0.89         ((r1_tarski @ sk_A @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B_2))),
% 0.71/0.89      inference('clc', [status(thm)], ['33', '42'])).
% 0.71/0.89  thf('44', plain,
% 0.71/0.89      (![X4 : $i, X6 : $i]:
% 0.71/0.89         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.71/0.89      inference('cnf', [status(esa)], [d3_tarski])).
% 0.71/0.89  thf('45', plain,
% 0.71/0.89      (((r1_tarski @ sk_A @ sk_B_2) | (r1_tarski @ sk_A @ sk_B_2))),
% 0.71/0.89      inference('sup-', [status(thm)], ['43', '44'])).
% 0.71/0.89  thf('46', plain, ((r1_tarski @ sk_A @ sk_B_2)),
% 0.71/0.89      inference('simplify', [status(thm)], ['45'])).
% 0.71/0.89  thf('47', plain, ($false), inference('demod', [status(thm)], ['24', '46'])).
% 0.71/0.89  
% 0.71/0.89  % SZS output end Refutation
% 0.71/0.89  
% 0.74/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
