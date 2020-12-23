%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vHzMBoC7PG

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:59 EST 2020

% Result     : Theorem 8.10s
% Output     : Refutation 8.10s
% Verified   : 
% Statistics : Number of formulae       :   47 (  62 expanded)
%              Number of leaves         :   10 (  22 expanded)
%              Depth                    :   14
%              Number of atoms          :  436 ( 600 expanded)
%              Number of equality atoms :    4 (  10 expanded)
%              Maximal formula depth    :   12 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t34_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ sk_C_1 @ sk_B ) @ ( k4_xboole_0 @ sk_C_1 @ sk_A ) ) ),
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

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('3',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ( r2_hidden @ X4 @ X7 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('6',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ X3 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ ( k4_xboole_0 @ X0 @ X3 ) ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X2 ) ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ X2 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ X2 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X2 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X2 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ X0 @ sk_A ) @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('23',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('24',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_B ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_B ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_B ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_B ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k4_xboole_0 @ X0 @ sk_B ) ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','29'])).

thf('31',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_B ) @ X1 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( k4_xboole_0 @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_B ) @ ( k4_xboole_0 @ X0 @ sk_A ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_B ) @ ( k4_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_B ) @ ( k4_xboole_0 @ X0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['0','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vHzMBoC7PG
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:11:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 8.10/8.37  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 8.10/8.37  % Solved by: fo/fo7.sh
% 8.10/8.37  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.10/8.37  % done 10455 iterations in 7.913s
% 8.10/8.37  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 8.10/8.37  % SZS output start Refutation
% 8.10/8.37  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 8.10/8.37  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 8.10/8.37  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 8.10/8.37  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.10/8.37  thf(sk_B_type, type, sk_B: $i).
% 8.10/8.37  thf(sk_C_1_type, type, sk_C_1: $i).
% 8.10/8.37  thf(sk_A_type, type, sk_A: $i).
% 8.10/8.37  thf(t34_xboole_1, conjecture,
% 8.10/8.37    (![A:$i,B:$i,C:$i]:
% 8.10/8.37     ( ( r1_tarski @ A @ B ) =>
% 8.10/8.37       ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ))).
% 8.10/8.37  thf(zf_stmt_0, negated_conjecture,
% 8.10/8.37    (~( ![A:$i,B:$i,C:$i]:
% 8.10/8.37        ( ( r1_tarski @ A @ B ) =>
% 8.10/8.37          ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ) )),
% 8.10/8.37    inference('cnf.neg', [status(esa)], [t34_xboole_1])).
% 8.10/8.37  thf('0', plain,
% 8.10/8.37      (~ (r1_tarski @ (k4_xboole_0 @ sk_C_1 @ sk_B) @ 
% 8.10/8.37          (k4_xboole_0 @ sk_C_1 @ sk_A))),
% 8.10/8.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.10/8.37  thf(d3_tarski, axiom,
% 8.10/8.37    (![A:$i,B:$i]:
% 8.10/8.37     ( ( r1_tarski @ A @ B ) <=>
% 8.10/8.37       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 8.10/8.37  thf('1', plain,
% 8.10/8.37      (![X1 : $i, X3 : $i]:
% 8.10/8.37         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 8.10/8.37      inference('cnf', [status(esa)], [d3_tarski])).
% 8.10/8.37  thf(d5_xboole_0, axiom,
% 8.10/8.37    (![A:$i,B:$i,C:$i]:
% 8.10/8.37     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 8.10/8.37       ( ![D:$i]:
% 8.10/8.37         ( ( r2_hidden @ D @ C ) <=>
% 8.10/8.37           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 8.10/8.37  thf('2', plain,
% 8.10/8.37      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 8.10/8.37         (~ (r2_hidden @ X8 @ X7)
% 8.10/8.37          | (r2_hidden @ X8 @ X5)
% 8.10/8.37          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 8.10/8.37      inference('cnf', [status(esa)], [d5_xboole_0])).
% 8.10/8.37  thf('3', plain,
% 8.10/8.37      (![X5 : $i, X6 : $i, X8 : $i]:
% 8.10/8.37         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 8.10/8.37      inference('simplify', [status(thm)], ['2'])).
% 8.10/8.37  thf('4', plain,
% 8.10/8.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.10/8.37         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 8.10/8.37          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 8.10/8.37      inference('sup-', [status(thm)], ['1', '3'])).
% 8.10/8.37  thf('5', plain,
% 8.10/8.37      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 8.10/8.37         (~ (r2_hidden @ X4 @ X5)
% 8.10/8.37          | (r2_hidden @ X4 @ X6)
% 8.10/8.37          | (r2_hidden @ X4 @ X7)
% 8.10/8.37          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 8.10/8.37      inference('cnf', [status(esa)], [d5_xboole_0])).
% 8.10/8.37  thf('6', plain,
% 8.10/8.37      (![X4 : $i, X5 : $i, X6 : $i]:
% 8.10/8.37         ((r2_hidden @ X4 @ (k4_xboole_0 @ X5 @ X6))
% 8.10/8.37          | (r2_hidden @ X4 @ X6)
% 8.10/8.37          | ~ (r2_hidden @ X4 @ X5))),
% 8.10/8.37      inference('simplify', [status(thm)], ['5'])).
% 8.10/8.37  thf('7', plain,
% 8.10/8.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.10/8.37         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2)
% 8.10/8.37          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X0 @ X1)) @ X3)
% 8.10/8.37          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X0 @ X1)) @ 
% 8.10/8.37             (k4_xboole_0 @ X0 @ X3)))),
% 8.10/8.37      inference('sup-', [status(thm)], ['4', '6'])).
% 8.10/8.37  thf('8', plain,
% 8.10/8.37      (![X1 : $i, X3 : $i]:
% 8.10/8.37         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 8.10/8.37      inference('cnf', [status(esa)], [d3_tarski])).
% 8.10/8.37  thf('9', plain,
% 8.10/8.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.10/8.37         ((r2_hidden @ 
% 8.10/8.37           (sk_C @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X2)) @ X0)
% 8.10/8.37          | (r1_tarski @ (k4_xboole_0 @ X1 @ X2) @ (k4_xboole_0 @ X1 @ X0))
% 8.10/8.37          | (r1_tarski @ (k4_xboole_0 @ X1 @ X2) @ (k4_xboole_0 @ X1 @ X0)))),
% 8.10/8.37      inference('sup-', [status(thm)], ['7', '8'])).
% 8.10/8.37  thf('10', plain,
% 8.10/8.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.10/8.37         ((r1_tarski @ (k4_xboole_0 @ X1 @ X2) @ (k4_xboole_0 @ X1 @ X0))
% 8.10/8.37          | (r2_hidden @ 
% 8.10/8.37             (sk_C @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X2)) @ X0))),
% 8.10/8.37      inference('simplify', [status(thm)], ['9'])).
% 8.10/8.37  thf('11', plain,
% 8.10/8.37      (![X1 : $i, X3 : $i]:
% 8.10/8.37         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 8.10/8.37      inference('cnf', [status(esa)], [d3_tarski])).
% 8.10/8.37  thf('12', plain,
% 8.10/8.37      (![X1 : $i, X3 : $i]:
% 8.10/8.37         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 8.10/8.37      inference('cnf', [status(esa)], [d3_tarski])).
% 8.10/8.37  thf('13', plain,
% 8.10/8.37      (![X4 : $i, X5 : $i, X6 : $i]:
% 8.10/8.37         ((r2_hidden @ X4 @ (k4_xboole_0 @ X5 @ X6))
% 8.10/8.37          | (r2_hidden @ X4 @ X6)
% 8.10/8.37          | ~ (r2_hidden @ X4 @ X5))),
% 8.10/8.37      inference('simplify', [status(thm)], ['5'])).
% 8.10/8.37  thf('14', plain,
% 8.10/8.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.10/8.37         ((r1_tarski @ X0 @ X1)
% 8.10/8.37          | (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 8.10/8.37          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X2)))),
% 8.10/8.37      inference('sup-', [status(thm)], ['12', '13'])).
% 8.10/8.37  thf('15', plain,
% 8.10/8.37      (![X1 : $i, X3 : $i]:
% 8.10/8.37         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 8.10/8.37      inference('cnf', [status(esa)], [d3_tarski])).
% 8.10/8.37  thf('16', plain,
% 8.10/8.37      (![X0 : $i, X1 : $i]:
% 8.10/8.37         ((r2_hidden @ (sk_C @ (k4_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 8.10/8.37          | (r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 8.10/8.37          | (r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 8.10/8.37      inference('sup-', [status(thm)], ['14', '15'])).
% 8.10/8.37  thf('17', plain,
% 8.10/8.37      (![X0 : $i, X1 : $i]:
% 8.10/8.37         ((r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 8.10/8.37          | (r2_hidden @ (sk_C @ (k4_xboole_0 @ X1 @ X0) @ X1) @ X0))),
% 8.10/8.37      inference('simplify', [status(thm)], ['16'])).
% 8.10/8.37  thf('18', plain, ((r1_tarski @ sk_A @ sk_B)),
% 8.10/8.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.10/8.37  thf('19', plain,
% 8.10/8.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.10/8.37         (~ (r2_hidden @ X0 @ X1)
% 8.10/8.37          | (r2_hidden @ X0 @ X2)
% 8.10/8.37          | ~ (r1_tarski @ X1 @ X2))),
% 8.10/8.37      inference('cnf', [status(esa)], [d3_tarski])).
% 8.10/8.37  thf('20', plain,
% 8.10/8.37      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 8.10/8.37      inference('sup-', [status(thm)], ['18', '19'])).
% 8.10/8.37  thf('21', plain,
% 8.10/8.37      (![X0 : $i]:
% 8.10/8.37         ((r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ sk_A))
% 8.10/8.37          | (r2_hidden @ (sk_C @ (k4_xboole_0 @ X0 @ sk_A) @ X0) @ sk_B))),
% 8.10/8.37      inference('sup-', [status(thm)], ['17', '20'])).
% 8.10/8.37  thf('22', plain,
% 8.10/8.37      (![X1 : $i, X3 : $i]:
% 8.10/8.37         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 8.10/8.37      inference('cnf', [status(esa)], [d3_tarski])).
% 8.10/8.37  thf('23', plain,
% 8.10/8.37      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 8.10/8.37         (~ (r2_hidden @ X8 @ X7)
% 8.10/8.37          | ~ (r2_hidden @ X8 @ X6)
% 8.10/8.37          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 8.10/8.37      inference('cnf', [status(esa)], [d5_xboole_0])).
% 8.10/8.37  thf('24', plain,
% 8.10/8.37      (![X5 : $i, X6 : $i, X8 : $i]:
% 8.10/8.37         (~ (r2_hidden @ X8 @ X6)
% 8.10/8.37          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 8.10/8.37      inference('simplify', [status(thm)], ['23'])).
% 8.10/8.37  thf('25', plain,
% 8.10/8.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.10/8.37         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 8.10/8.37          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 8.10/8.37      inference('sup-', [status(thm)], ['22', '24'])).
% 8.10/8.37  thf('26', plain,
% 8.10/8.37      (![X0 : $i]:
% 8.10/8.37         ((r1_tarski @ (k4_xboole_0 @ X0 @ sk_B) @ 
% 8.10/8.37           (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A))
% 8.10/8.37          | (r1_tarski @ (k4_xboole_0 @ X0 @ sk_B) @ 
% 8.10/8.37             (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A)))),
% 8.10/8.37      inference('sup-', [status(thm)], ['21', '25'])).
% 8.10/8.37  thf('27', plain,
% 8.10/8.37      (![X0 : $i]:
% 8.10/8.37         (r1_tarski @ (k4_xboole_0 @ X0 @ sk_B) @ 
% 8.10/8.37          (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A))),
% 8.10/8.37      inference('simplify', [status(thm)], ['26'])).
% 8.10/8.37  thf('28', plain,
% 8.10/8.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.10/8.37         (~ (r2_hidden @ X0 @ X1)
% 8.10/8.37          | (r2_hidden @ X0 @ X2)
% 8.10/8.37          | ~ (r1_tarski @ X1 @ X2))),
% 8.10/8.37      inference('cnf', [status(esa)], [d3_tarski])).
% 8.10/8.37  thf('29', plain,
% 8.10/8.37      (![X0 : $i, X1 : $i]:
% 8.10/8.37         ((r2_hidden @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A))
% 8.10/8.37          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ sk_B)))),
% 8.10/8.37      inference('sup-', [status(thm)], ['27', '28'])).
% 8.10/8.37  thf('30', plain,
% 8.10/8.37      (![X0 : $i, X1 : $i]:
% 8.10/8.37         ((r1_tarski @ (k4_xboole_0 @ X0 @ sk_B) @ X1)
% 8.10/8.37          | (r2_hidden @ (sk_C @ X1 @ (k4_xboole_0 @ X0 @ sk_B)) @ 
% 8.10/8.37             (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A)))),
% 8.10/8.37      inference('sup-', [status(thm)], ['11', '29'])).
% 8.10/8.37  thf('31', plain,
% 8.10/8.37      (![X5 : $i, X6 : $i, X8 : $i]:
% 8.10/8.37         (~ (r2_hidden @ X8 @ X6)
% 8.10/8.37          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 8.10/8.37      inference('simplify', [status(thm)], ['23'])).
% 8.10/8.37  thf('32', plain,
% 8.10/8.37      (![X0 : $i, X1 : $i]:
% 8.10/8.37         ((r1_tarski @ (k4_xboole_0 @ X0 @ sk_B) @ X1)
% 8.10/8.37          | ~ (r2_hidden @ (sk_C @ X1 @ (k4_xboole_0 @ X0 @ sk_B)) @ sk_A))),
% 8.10/8.37      inference('sup-', [status(thm)], ['30', '31'])).
% 8.10/8.37  thf('33', plain,
% 8.10/8.37      (![X0 : $i]:
% 8.10/8.37         ((r1_tarski @ (k4_xboole_0 @ X0 @ sk_B) @ (k4_xboole_0 @ X0 @ sk_A))
% 8.10/8.37          | (r1_tarski @ (k4_xboole_0 @ X0 @ sk_B) @ (k4_xboole_0 @ X0 @ sk_A)))),
% 8.10/8.37      inference('sup-', [status(thm)], ['10', '32'])).
% 8.10/8.37  thf('34', plain,
% 8.10/8.37      (![X0 : $i]:
% 8.10/8.37         (r1_tarski @ (k4_xboole_0 @ X0 @ sk_B) @ (k4_xboole_0 @ X0 @ sk_A))),
% 8.10/8.37      inference('simplify', [status(thm)], ['33'])).
% 8.10/8.37  thf('35', plain, ($false), inference('demod', [status(thm)], ['0', '34'])).
% 8.10/8.37  
% 8.10/8.37  % SZS output end Refutation
% 8.10/8.37  
% 8.10/8.38  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
