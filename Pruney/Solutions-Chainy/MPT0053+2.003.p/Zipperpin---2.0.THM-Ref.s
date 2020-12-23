%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xm0fOInfv5

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:06 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 163 expanded)
%              Number of leaves         :   13 (  55 expanded)
%              Depth                    :   13
%              Number of atoms          :  392 (1282 expanded)
%              Number of equality atoms :   36 ( 133 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('2',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('3',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('6',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X9 @ X10 ) @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('11',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('12',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('15',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ k1_xboole_0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('23',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','24'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(t46_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t46_xboole_1])).

thf('28',plain,(
    ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_A @ sk_B ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('30',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ( k4_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ k1_xboole_0 ) @ X0 ) ),
    inference('simplify_reflect-',[status(thm)],['18','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('38',plain,(
    $false ),
    inference('sup-',[status(thm)],['36','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xm0fOInfv5
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:01:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.69/0.93  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.69/0.93  % Solved by: fo/fo7.sh
% 0.69/0.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.93  % done 767 iterations in 0.464s
% 0.69/0.93  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.69/0.93  % SZS output start Refutation
% 0.69/0.93  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.93  thf(sk_B_type, type, sk_B: $i).
% 0.69/0.93  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.69/0.93  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.69/0.93  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.69/0.93  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.69/0.93  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.69/0.93  thf(d5_xboole_0, axiom,
% 0.69/0.93    (![A:$i,B:$i,C:$i]:
% 0.69/0.93     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.69/0.93       ( ![D:$i]:
% 0.69/0.93         ( ( r2_hidden @ D @ C ) <=>
% 0.69/0.93           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.69/0.93  thf('0', plain,
% 0.69/0.93      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.69/0.93         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 0.69/0.93          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.69/0.93          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.69/0.93      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.69/0.93  thf('1', plain,
% 0.69/0.93      (![X0 : $i, X1 : $i]:
% 0.69/0.93         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.69/0.93          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.69/0.93      inference('eq_fact', [status(thm)], ['0'])).
% 0.69/0.93  thf('2', plain,
% 0.69/0.93      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.69/0.93         (~ (r2_hidden @ X2 @ X3)
% 0.69/0.93          | (r2_hidden @ X2 @ X4)
% 0.69/0.93          | (r2_hidden @ X2 @ X5)
% 0.69/0.93          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.69/0.93      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.69/0.93  thf('3', plain,
% 0.69/0.93      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.69/0.93         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 0.69/0.93          | (r2_hidden @ X2 @ X4)
% 0.69/0.93          | ~ (r2_hidden @ X2 @ X3))),
% 0.69/0.93      inference('simplify', [status(thm)], ['2'])).
% 0.69/0.93  thf('4', plain,
% 0.69/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.93         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 0.69/0.93          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X2)
% 0.69/0.93          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X2)))),
% 0.69/0.93      inference('sup-', [status(thm)], ['1', '3'])).
% 0.69/0.93  thf(commutativity_k2_xboole_0, axiom,
% 0.69/0.93    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.69/0.93  thf('5', plain,
% 0.69/0.93      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.69/0.93      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.69/0.93  thf(t1_boole, axiom,
% 0.69/0.93    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.69/0.93  thf('6', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.69/0.93      inference('cnf', [status(esa)], [t1_boole])).
% 0.69/0.93  thf('7', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.69/0.93      inference('sup+', [status(thm)], ['5', '6'])).
% 0.69/0.93  thf(t40_xboole_1, axiom,
% 0.69/0.93    (![A:$i,B:$i]:
% 0.69/0.93     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.69/0.93  thf('8', plain,
% 0.69/0.93      (![X9 : $i, X10 : $i]:
% 0.69/0.93         ((k4_xboole_0 @ (k2_xboole_0 @ X9 @ X10) @ X10)
% 0.69/0.93           = (k4_xboole_0 @ X9 @ X10))),
% 0.69/0.93      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.69/0.93  thf('9', plain,
% 0.69/0.93      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.69/0.93      inference('sup+', [status(thm)], ['7', '8'])).
% 0.69/0.93  thf('10', plain,
% 0.69/0.93      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.69/0.93      inference('sup+', [status(thm)], ['7', '8'])).
% 0.69/0.93  thf('11', plain,
% 0.69/0.93      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.69/0.93         (~ (r2_hidden @ X6 @ X5)
% 0.69/0.93          | ~ (r2_hidden @ X6 @ X4)
% 0.69/0.93          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.69/0.93      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.69/0.93  thf('12', plain,
% 0.69/0.93      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.69/0.93         (~ (r2_hidden @ X6 @ X4)
% 0.69/0.93          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.69/0.93      inference('simplify', [status(thm)], ['11'])).
% 0.69/0.93  thf('13', plain,
% 0.69/0.93      (![X0 : $i, X1 : $i]:
% 0.69/0.93         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.69/0.93          | ~ (r2_hidden @ X1 @ X0))),
% 0.69/0.93      inference('sup-', [status(thm)], ['10', '12'])).
% 0.69/0.93  thf('14', plain,
% 0.69/0.93      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.69/0.93         (~ (r2_hidden @ X6 @ X5)
% 0.69/0.93          | (r2_hidden @ X6 @ X3)
% 0.69/0.93          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.69/0.93      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.69/0.93  thf('15', plain,
% 0.69/0.93      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.69/0.93         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.69/0.93      inference('simplify', [status(thm)], ['14'])).
% 0.69/0.93  thf('16', plain,
% 0.69/0.93      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.69/0.93      inference('clc', [status(thm)], ['13', '15'])).
% 0.69/0.93  thf('17', plain,
% 0.69/0.93      (![X0 : $i, X1 : $i]:
% 0.69/0.93         ~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.69/0.93      inference('sup-', [status(thm)], ['9', '16'])).
% 0.69/0.93  thf('18', plain,
% 0.69/0.93      (![X0 : $i, X1 : $i]:
% 0.69/0.93         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ k1_xboole_0) @ X0)
% 0.69/0.93          | ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X1)))),
% 0.69/0.93      inference('sup-', [status(thm)], ['4', '17'])).
% 0.69/0.93  thf('19', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.69/0.93      inference('sup+', [status(thm)], ['5', '6'])).
% 0.69/0.93  thf('20', plain,
% 0.69/0.93      (![X0 : $i, X1 : $i]:
% 0.69/0.93         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.69/0.93          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.69/0.93      inference('eq_fact', [status(thm)], ['0'])).
% 0.69/0.93  thf('21', plain,
% 0.69/0.93      (![X0 : $i, X1 : $i]:
% 0.69/0.93         ~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.69/0.93      inference('sup-', [status(thm)], ['9', '16'])).
% 0.69/0.93  thf('22', plain,
% 0.69/0.93      (![X0 : $i, X1 : $i]:
% 0.69/0.93         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.69/0.93           = (k4_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0) @ X1))),
% 0.69/0.93      inference('sup-', [status(thm)], ['20', '21'])).
% 0.69/0.93  thf(t41_xboole_1, axiom,
% 0.69/0.93    (![A:$i,B:$i,C:$i]:
% 0.69/0.93     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.69/0.93       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.69/0.93  thf('23', plain,
% 0.69/0.93      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.69/0.93         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 0.69/0.93           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.69/0.93      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.69/0.93  thf('24', plain,
% 0.69/0.93      (![X0 : $i, X1 : $i]:
% 0.69/0.93         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.69/0.93           = (k4_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.69/0.93      inference('demod', [status(thm)], ['22', '23'])).
% 0.69/0.93  thf('25', plain,
% 0.69/0.93      (![X0 : $i]:
% 0.69/0.93         ((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.69/0.93           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.69/0.93      inference('sup+', [status(thm)], ['19', '24'])).
% 0.69/0.93  thf('26', plain,
% 0.69/0.93      (![X0 : $i]:
% 0.69/0.93         ((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.69/0.93           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.69/0.93      inference('sup+', [status(thm)], ['19', '24'])).
% 0.69/0.93  thf('27', plain,
% 0.69/0.93      (![X0 : $i, X1 : $i]:
% 0.69/0.93         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X1))),
% 0.69/0.93      inference('sup+', [status(thm)], ['25', '26'])).
% 0.69/0.93  thf(t46_xboole_1, conjecture,
% 0.69/0.93    (![A:$i,B:$i]:
% 0.69/0.93     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.69/0.93  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.93    (~( ![A:$i,B:$i]:
% 0.69/0.93        ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ) )),
% 0.69/0.93    inference('cnf.neg', [status(esa)], [t46_xboole_1])).
% 0.69/0.93  thf('28', plain,
% 0.69/0.93      (((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_A @ sk_B)) != (k1_xboole_0))),
% 0.69/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.93  thf('29', plain,
% 0.69/0.93      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.69/0.93      inference('sup+', [status(thm)], ['7', '8'])).
% 0.69/0.93  thf('30', plain,
% 0.69/0.93      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.69/0.93         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 0.69/0.93           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.69/0.93      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.69/0.93  thf('31', plain,
% 0.69/0.93      (![X0 : $i, X1 : $i]:
% 0.69/0.93         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 0.69/0.93           = (k4_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.69/0.93      inference('sup+', [status(thm)], ['29', '30'])).
% 0.69/0.93  thf('32', plain,
% 0.69/0.93      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.69/0.93         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 0.69/0.93           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.69/0.93      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.69/0.93  thf('33', plain,
% 0.69/0.93      (![X0 : $i, X1 : $i]:
% 0.69/0.93         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.69/0.93           = (k4_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.69/0.93      inference('demod', [status(thm)], ['31', '32'])).
% 0.69/0.93  thf('34', plain,
% 0.69/0.93      (((k4_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B))
% 0.69/0.93         != (k1_xboole_0))),
% 0.69/0.93      inference('demod', [status(thm)], ['28', '33'])).
% 0.69/0.93  thf('35', plain,
% 0.69/0.93      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) != (k1_xboole_0))),
% 0.69/0.93      inference('sup-', [status(thm)], ['27', '34'])).
% 0.69/0.93  thf('36', plain,
% 0.69/0.93      (![X0 : $i, X1 : $i]:
% 0.69/0.93         (r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ k1_xboole_0) @ X0)),
% 0.69/0.93      inference('simplify_reflect-', [status(thm)], ['18', '35'])).
% 0.69/0.93  thf('37', plain,
% 0.69/0.93      (![X0 : $i, X1 : $i]:
% 0.69/0.93         ~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.69/0.93      inference('sup-', [status(thm)], ['9', '16'])).
% 0.69/0.93  thf('38', plain, ($false), inference('sup-', [status(thm)], ['36', '37'])).
% 0.69/0.93  
% 0.69/0.93  % SZS output end Refutation
% 0.69/0.93  
% 0.78/0.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
