%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.swCf51L28o

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:06 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   49 (  56 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :   12
%              Number of atoms          :  298 ( 367 expanded)
%              Number of equality atoms :   19 (  21 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t73_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ C ) )
       => ( r1_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t73_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X15: $i,X17: $i] :
      ( ( ( k4_xboole_0 @ X15 @ X17 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('3',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X25 @ X26 ) @ X27 )
      = ( k4_xboole_0 @ X25 @ ( k2_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ( ( k4_xboole_0 @ X15 @ X16 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C_1 ),
    inference(simplify,[status(thm)],['7'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('10',plain,
    ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('12',plain,(
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

thf('13',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X7 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('14',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('19',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ X28 @ X29 )
      | ~ ( r1_xboole_0 @ X29 @ X30 )
      | ( r1_xboole_0 @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['11','20'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('22',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['10','23'])).

thf('25',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ( ( k4_xboole_0 @ X15 @ X16 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('26',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    $false ),
    inference(demod,[status(thm)],['0','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.swCf51L28o
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:33:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.39/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.62  % Solved by: fo/fo7.sh
% 0.39/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.62  % done 552 iterations in 0.177s
% 0.39/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.62  % SZS output start Refutation
% 0.39/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.62  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.39/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.39/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.39/0.62  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.39/0.62  thf(t73_xboole_1, conjecture,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.39/0.62       ( r1_tarski @ A @ B ) ))).
% 0.39/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.62    (~( ![A:$i,B:$i,C:$i]:
% 0.39/0.62        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 0.39/0.62            ( r1_xboole_0 @ A @ C ) ) =>
% 0.39/0.62          ( r1_tarski @ A @ B ) ) )),
% 0.39/0.62    inference('cnf.neg', [status(esa)], [t73_xboole_1])).
% 0.39/0.62  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('1', plain, ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(l32_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.39/0.62  thf('2', plain,
% 0.39/0.62      (![X15 : $i, X17 : $i]:
% 0.39/0.62         (((k4_xboole_0 @ X15 @ X17) = (k1_xboole_0))
% 0.39/0.62          | ~ (r1_tarski @ X15 @ X17))),
% 0.39/0.62      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.39/0.62  thf('3', plain,
% 0.39/0.62      (((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)) = (k1_xboole_0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.62  thf(t41_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.39/0.62       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.39/0.62  thf('4', plain,
% 0.39/0.62      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.39/0.62         ((k4_xboole_0 @ (k4_xboole_0 @ X25 @ X26) @ X27)
% 0.39/0.62           = (k4_xboole_0 @ X25 @ (k2_xboole_0 @ X26 @ X27)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.39/0.62  thf('5', plain,
% 0.39/0.62      (![X15 : $i, X16 : $i]:
% 0.39/0.62         ((r1_tarski @ X15 @ X16)
% 0.39/0.62          | ((k4_xboole_0 @ X15 @ X16) != (k1_xboole_0)))),
% 0.39/0.62      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.39/0.62  thf('6', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.62         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.39/0.62          | (r1_tarski @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['4', '5'])).
% 0.39/0.62  thf('7', plain,
% 0.39/0.62      ((((k1_xboole_0) != (k1_xboole_0))
% 0.39/0.62        | (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C_1))),
% 0.39/0.62      inference('sup-', [status(thm)], ['3', '6'])).
% 0.39/0.62  thf('8', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C_1)),
% 0.39/0.62      inference('simplify', [status(thm)], ['7'])).
% 0.39/0.62  thf(t28_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.39/0.62  thf('9', plain,
% 0.39/0.62      (![X21 : $i, X22 : $i]:
% 0.39/0.62         (((k3_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_tarski @ X21 @ X22))),
% 0.39/0.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.39/0.62  thf('10', plain,
% 0.39/0.62      (((k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C_1)
% 0.39/0.62         = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.39/0.62      inference('sup-', [status(thm)], ['8', '9'])).
% 0.39/0.62  thf('11', plain, ((r1_xboole_0 @ sk_A @ sk_C_1)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(d3_tarski, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( r1_tarski @ A @ B ) <=>
% 0.39/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.39/0.62  thf('12', plain,
% 0.39/0.62      (![X3 : $i, X5 : $i]:
% 0.39/0.62         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.39/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.62  thf(d5_xboole_0, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.39/0.62       ( ![D:$i]:
% 0.39/0.62         ( ( r2_hidden @ D @ C ) <=>
% 0.39/0.62           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.39/0.62  thf('13', plain,
% 0.39/0.62      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.39/0.62         (~ (r2_hidden @ X10 @ X9)
% 0.39/0.62          | (r2_hidden @ X10 @ X7)
% 0.39/0.62          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.39/0.62      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.39/0.62  thf('14', plain,
% 0.39/0.62      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.39/0.62         ((r2_hidden @ X10 @ X7)
% 0.39/0.62          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['13'])).
% 0.39/0.62  thf('15', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.62         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.39/0.62          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.39/0.62      inference('sup-', [status(thm)], ['12', '14'])).
% 0.39/0.62  thf('16', plain,
% 0.39/0.62      (![X3 : $i, X5 : $i]:
% 0.39/0.62         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.39/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.62  thf('17', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.39/0.62          | (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['15', '16'])).
% 0.39/0.62  thf('18', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.39/0.62      inference('simplify', [status(thm)], ['17'])).
% 0.39/0.62  thf(t63_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.39/0.62       ( r1_xboole_0 @ A @ C ) ))).
% 0.39/0.62  thf('19', plain,
% 0.39/0.62      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.39/0.62         (~ (r1_tarski @ X28 @ X29)
% 0.39/0.62          | ~ (r1_xboole_0 @ X29 @ X30)
% 0.39/0.62          | (r1_xboole_0 @ X28 @ X30))),
% 0.39/0.62      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.39/0.62  thf('20', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.62         ((r1_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)
% 0.39/0.62          | ~ (r1_xboole_0 @ X0 @ X2))),
% 0.39/0.62      inference('sup-', [status(thm)], ['18', '19'])).
% 0.39/0.62  thf('21', plain,
% 0.39/0.62      (![X0 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ sk_C_1)),
% 0.39/0.62      inference('sup-', [status(thm)], ['11', '20'])).
% 0.39/0.62  thf(d7_xboole_0, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.39/0.62       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.39/0.62  thf('22', plain,
% 0.39/0.62      (![X12 : $i, X13 : $i]:
% 0.39/0.62         (((k3_xboole_0 @ X12 @ X13) = (k1_xboole_0))
% 0.39/0.62          | ~ (r1_xboole_0 @ X12 @ X13))),
% 0.39/0.62      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.39/0.62  thf('23', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((k3_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ sk_C_1) = (k1_xboole_0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['21', '22'])).
% 0.39/0.62  thf('24', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.39/0.62      inference('demod', [status(thm)], ['10', '23'])).
% 0.39/0.62  thf('25', plain,
% 0.39/0.62      (![X15 : $i, X16 : $i]:
% 0.39/0.62         ((r1_tarski @ X15 @ X16)
% 0.39/0.62          | ((k4_xboole_0 @ X15 @ X16) != (k1_xboole_0)))),
% 0.39/0.62      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.39/0.62  thf('26', plain,
% 0.39/0.62      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 0.39/0.62      inference('sup-', [status(thm)], ['24', '25'])).
% 0.39/0.62  thf('27', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.39/0.62      inference('simplify', [status(thm)], ['26'])).
% 0.39/0.62  thf('28', plain, ($false), inference('demod', [status(thm)], ['0', '27'])).
% 0.39/0.62  
% 0.39/0.62  % SZS output end Refutation
% 0.39/0.62  
% 0.39/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
