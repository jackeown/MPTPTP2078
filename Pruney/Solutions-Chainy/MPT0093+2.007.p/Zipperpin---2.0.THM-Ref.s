%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jhikGkCxfJ

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:47 EST 2020

% Result     : Theorem 2.13s
% Output     : Refutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   48 (  62 expanded)
%              Number of leaves         :   12 (  23 expanded)
%              Depth                    :   14
%              Number of atoms          :  385 ( 534 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
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

thf(t86_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_xboole_0 @ A @ C ) )
       => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t86_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_2 ) ) ),
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
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ( r2_hidden @ X4 @ X7 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('7',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) @ X0 )
      | ( r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      | ( r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    r1_xboole_0 @ sk_A @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

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

thf('21',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r1_xboole_0 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['13','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_A @ sk_C_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k4_xboole_0 @ sk_A @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['12','27'])).

thf('29',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('30',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,
    ( ( r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['11','31'])).

thf('33',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['0','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jhikGkCxfJ
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:37:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.13/2.38  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.13/2.38  % Solved by: fo/fo7.sh
% 2.13/2.38  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.13/2.38  % done 3727 iterations in 1.910s
% 2.13/2.38  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.13/2.38  % SZS output start Refutation
% 2.13/2.38  thf(sk_C_2_type, type, sk_C_2: $i).
% 2.13/2.38  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.13/2.38  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.13/2.38  thf(sk_B_type, type, sk_B: $i).
% 2.13/2.38  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.13/2.38  thf(sk_A_type, type, sk_A: $i).
% 2.13/2.38  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.13/2.38  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.13/2.38  thf(t86_xboole_1, conjecture,
% 2.13/2.38    (![A:$i,B:$i,C:$i]:
% 2.13/2.38     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 2.13/2.38       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 2.13/2.38  thf(zf_stmt_0, negated_conjecture,
% 2.13/2.38    (~( ![A:$i,B:$i,C:$i]:
% 2.13/2.38        ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 2.13/2.38          ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )),
% 2.13/2.38    inference('cnf.neg', [status(esa)], [t86_xboole_1])).
% 2.13/2.38  thf('0', plain, (~ (r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_2))),
% 2.13/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.38  thf(d3_tarski, axiom,
% 2.13/2.38    (![A:$i,B:$i]:
% 2.13/2.38     ( ( r1_tarski @ A @ B ) <=>
% 2.13/2.38       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.13/2.38  thf('1', plain,
% 2.13/2.38      (![X1 : $i, X3 : $i]:
% 2.13/2.38         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 2.13/2.38      inference('cnf', [status(esa)], [d3_tarski])).
% 2.13/2.38  thf('2', plain, ((r1_tarski @ sk_A @ sk_B)),
% 2.13/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.38  thf('3', plain,
% 2.13/2.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.13/2.38         (~ (r2_hidden @ X0 @ X1)
% 2.13/2.38          | (r2_hidden @ X0 @ X2)
% 2.13/2.38          | ~ (r1_tarski @ X1 @ X2))),
% 2.13/2.38      inference('cnf', [status(esa)], [d3_tarski])).
% 2.13/2.38  thf('4', plain,
% 2.13/2.38      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 2.13/2.38      inference('sup-', [status(thm)], ['2', '3'])).
% 2.13/2.38  thf('5', plain,
% 2.13/2.38      (![X0 : $i]:
% 2.13/2.38         ((r1_tarski @ sk_A @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 2.13/2.38      inference('sup-', [status(thm)], ['1', '4'])).
% 2.13/2.38  thf(d5_xboole_0, axiom,
% 2.13/2.38    (![A:$i,B:$i,C:$i]:
% 2.13/2.38     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 2.13/2.38       ( ![D:$i]:
% 2.13/2.38         ( ( r2_hidden @ D @ C ) <=>
% 2.13/2.38           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 2.13/2.38  thf('6', plain,
% 2.13/2.38      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 2.13/2.38         (~ (r2_hidden @ X4 @ X5)
% 2.13/2.38          | (r2_hidden @ X4 @ X6)
% 2.13/2.38          | (r2_hidden @ X4 @ X7)
% 2.13/2.38          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 2.13/2.38      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.13/2.38  thf('7', plain,
% 2.13/2.38      (![X4 : $i, X5 : $i, X6 : $i]:
% 2.13/2.38         ((r2_hidden @ X4 @ (k4_xboole_0 @ X5 @ X6))
% 2.13/2.38          | (r2_hidden @ X4 @ X6)
% 2.13/2.38          | ~ (r2_hidden @ X4 @ X5))),
% 2.13/2.38      inference('simplify', [status(thm)], ['6'])).
% 2.13/2.38  thf('8', plain,
% 2.13/2.38      (![X0 : $i, X1 : $i]:
% 2.13/2.38         ((r1_tarski @ sk_A @ X0)
% 2.13/2.38          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ X1)
% 2.13/2.38          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ (k4_xboole_0 @ sk_B @ X1)))),
% 2.13/2.38      inference('sup-', [status(thm)], ['5', '7'])).
% 2.13/2.38  thf('9', plain,
% 2.13/2.38      (![X1 : $i, X3 : $i]:
% 2.13/2.38         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 2.13/2.38      inference('cnf', [status(esa)], [d3_tarski])).
% 2.13/2.38  thf('10', plain,
% 2.13/2.38      (![X0 : $i]:
% 2.13/2.38         ((r2_hidden @ (sk_C @ (k4_xboole_0 @ sk_B @ X0) @ sk_A) @ X0)
% 2.13/2.38          | (r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 2.13/2.38          | (r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ X0)))),
% 2.13/2.38      inference('sup-', [status(thm)], ['8', '9'])).
% 2.13/2.38  thf('11', plain,
% 2.13/2.38      (![X0 : $i]:
% 2.13/2.38         ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 2.13/2.38          | (r2_hidden @ (sk_C @ (k4_xboole_0 @ sk_B @ X0) @ sk_A) @ X0))),
% 2.13/2.38      inference('simplify', [status(thm)], ['10'])).
% 2.13/2.38  thf('12', plain,
% 2.13/2.38      (![X1 : $i, X3 : $i]:
% 2.13/2.38         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 2.13/2.38      inference('cnf', [status(esa)], [d3_tarski])).
% 2.13/2.38  thf('13', plain, ((r1_xboole_0 @ sk_A @ sk_C_2)),
% 2.13/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.38  thf('14', plain,
% 2.13/2.38      (![X1 : $i, X3 : $i]:
% 2.13/2.38         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 2.13/2.38      inference('cnf', [status(esa)], [d3_tarski])).
% 2.13/2.38  thf('15', plain,
% 2.13/2.38      (![X4 : $i, X5 : $i, X6 : $i]:
% 2.13/2.38         ((r2_hidden @ X4 @ (k4_xboole_0 @ X5 @ X6))
% 2.13/2.38          | (r2_hidden @ X4 @ X6)
% 2.13/2.38          | ~ (r2_hidden @ X4 @ X5))),
% 2.13/2.38      inference('simplify', [status(thm)], ['6'])).
% 2.13/2.38  thf('16', plain,
% 2.13/2.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.13/2.38         ((r1_tarski @ X0 @ X1)
% 2.13/2.38          | (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 2.13/2.38          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X2)))),
% 2.13/2.38      inference('sup-', [status(thm)], ['14', '15'])).
% 2.13/2.38  thf('17', plain,
% 2.13/2.38      (![X1 : $i, X3 : $i]:
% 2.13/2.38         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 2.13/2.38      inference('cnf', [status(esa)], [d3_tarski])).
% 2.13/2.38  thf('18', plain,
% 2.13/2.38      (![X0 : $i, X1 : $i]:
% 2.13/2.38         ((r2_hidden @ (sk_C @ (k4_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 2.13/2.38          | (r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 2.13/2.38          | (r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.13/2.38      inference('sup-', [status(thm)], ['16', '17'])).
% 2.13/2.38  thf('19', plain,
% 2.13/2.38      (![X0 : $i, X1 : $i]:
% 2.13/2.38         ((r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 2.13/2.38          | (r2_hidden @ (sk_C @ (k4_xboole_0 @ X1 @ X0) @ X1) @ X0))),
% 2.13/2.38      inference('simplify', [status(thm)], ['18'])).
% 2.13/2.38  thf('20', plain,
% 2.13/2.38      (![X1 : $i, X3 : $i]:
% 2.13/2.38         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 2.13/2.38      inference('cnf', [status(esa)], [d3_tarski])).
% 2.13/2.38  thf(t3_xboole_0, axiom,
% 2.13/2.38    (![A:$i,B:$i]:
% 2.13/2.38     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 2.13/2.38            ( r1_xboole_0 @ A @ B ) ) ) & 
% 2.13/2.38       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 2.13/2.38            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 2.13/2.38  thf('21', plain,
% 2.13/2.38      (![X10 : $i, X12 : $i, X13 : $i]:
% 2.13/2.38         (~ (r2_hidden @ X12 @ X10)
% 2.13/2.38          | ~ (r2_hidden @ X12 @ X13)
% 2.13/2.38          | ~ (r1_xboole_0 @ X10 @ X13))),
% 2.13/2.38      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.13/2.38  thf('22', plain,
% 2.13/2.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.13/2.38         ((r1_tarski @ X0 @ X1)
% 2.13/2.38          | ~ (r1_xboole_0 @ X0 @ X2)
% 2.13/2.38          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 2.13/2.38      inference('sup-', [status(thm)], ['20', '21'])).
% 2.13/2.38  thf('23', plain,
% 2.13/2.38      (![X0 : $i, X1 : $i]:
% 2.13/2.38         ((r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 2.13/2.38          | ~ (r1_xboole_0 @ X1 @ X0)
% 2.13/2.38          | (r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.13/2.38      inference('sup-', [status(thm)], ['19', '22'])).
% 2.13/2.38  thf('24', plain,
% 2.13/2.38      (![X0 : $i, X1 : $i]:
% 2.13/2.38         (~ (r1_xboole_0 @ X1 @ X0)
% 2.13/2.38          | (r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.13/2.38      inference('simplify', [status(thm)], ['23'])).
% 2.13/2.38  thf('25', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C_2))),
% 2.13/2.38      inference('sup-', [status(thm)], ['13', '24'])).
% 2.13/2.38  thf('26', plain,
% 2.13/2.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.13/2.38         (~ (r2_hidden @ X0 @ X1)
% 2.13/2.38          | (r2_hidden @ X0 @ X2)
% 2.13/2.38          | ~ (r1_tarski @ X1 @ X2))),
% 2.13/2.38      inference('cnf', [status(esa)], [d3_tarski])).
% 2.13/2.38  thf('27', plain,
% 2.13/2.38      (![X0 : $i]:
% 2.13/2.38         ((r2_hidden @ X0 @ (k4_xboole_0 @ sk_A @ sk_C_2))
% 2.13/2.38          | ~ (r2_hidden @ X0 @ sk_A))),
% 2.13/2.38      inference('sup-', [status(thm)], ['25', '26'])).
% 2.13/2.38  thf('28', plain,
% 2.13/2.38      (![X0 : $i]:
% 2.13/2.38         ((r1_tarski @ sk_A @ X0)
% 2.13/2.38          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ (k4_xboole_0 @ sk_A @ sk_C_2)))),
% 2.13/2.38      inference('sup-', [status(thm)], ['12', '27'])).
% 2.13/2.38  thf('29', plain,
% 2.13/2.38      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 2.13/2.38         (~ (r2_hidden @ X8 @ X7)
% 2.13/2.38          | ~ (r2_hidden @ X8 @ X6)
% 2.13/2.38          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 2.13/2.38      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.13/2.38  thf('30', plain,
% 2.13/2.38      (![X5 : $i, X6 : $i, X8 : $i]:
% 2.13/2.38         (~ (r2_hidden @ X8 @ X6)
% 2.13/2.38          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 2.13/2.38      inference('simplify', [status(thm)], ['29'])).
% 2.13/2.38  thf('31', plain,
% 2.13/2.38      (![X0 : $i]:
% 2.13/2.38         ((r1_tarski @ sk_A @ X0) | ~ (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_C_2))),
% 2.13/2.38      inference('sup-', [status(thm)], ['28', '30'])).
% 2.13/2.38  thf('32', plain,
% 2.13/2.38      (((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_2))
% 2.13/2.38        | (r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_2)))),
% 2.13/2.38      inference('sup-', [status(thm)], ['11', '31'])).
% 2.13/2.38  thf('33', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_2))),
% 2.13/2.38      inference('simplify', [status(thm)], ['32'])).
% 2.13/2.38  thf('34', plain, ($false), inference('demod', [status(thm)], ['0', '33'])).
% 2.13/2.38  
% 2.13/2.38  % SZS output end Refutation
% 2.13/2.38  
% 2.13/2.39  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
