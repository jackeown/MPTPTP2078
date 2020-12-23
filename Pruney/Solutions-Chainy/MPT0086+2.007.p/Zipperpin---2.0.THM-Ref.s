%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KnPvJtMTdY

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:29 EST 2020

% Result     : Theorem 2.06s
% Output     : Refutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   53 (  90 expanded)
%              Number of leaves         :   17 (  32 expanded)
%              Depth                    :   16
%              Number of atoms          :  348 ( 682 expanded)
%              Number of equality atoms :   24 (  40 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t79_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) ),
    inference('cnf.neg',[status(esa)],[t79_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i,X10: $i] :
      ( ( X10
        = ( k3_xboole_0 @ X6 @ X7 ) )
      | ( r2_hidden @ ( sk_D @ X10 @ X7 @ X6 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X10 @ X7 @ X6 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X6: $i,X7: $i,X10: $i] :
      ( ( X10
        = ( k3_xboole_0 @ X6 @ X7 ) )
      | ( r2_hidden @ ( sk_D @ X10 @ X7 @ X6 ) @ X7 )
      | ( r2_hidden @ ( sk_D @ X10 @ X7 @ X6 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('5',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X14 )
      | ( r2_hidden @ X15 @ X12 )
      | ( X14
       != ( k4_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('7',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ( r2_hidden @ X15 @ X12 )
      | ~ ( r2_hidden @ X15 @ ( k4_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('10',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X14 )
      | ~ ( r2_hidden @ X15 @ X13 )
      | ( X14
       != ( k4_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('11',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X13 )
      | ~ ( r2_hidden @ X15 @ ( k4_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ( v1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('15',plain,(
    ! [X20: $i] :
      ( ( X20 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X13 )
      | ~ ( r2_hidden @ X15 @ ( k4_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','19'])).

thf('21',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X13 )
      | ~ ( r2_hidden @ X15 @ ( k4_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('26',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('30',plain,(
    ! [X17: $i,X19: $i] :
      ( ( r1_xboole_0 @ X17 @ X19 )
      | ( ( k3_xboole_0 @ X17 @ X19 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['0','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KnPvJtMTdY
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:20:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.06/2.25  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.06/2.25  % Solved by: fo/fo7.sh
% 2.06/2.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.06/2.25  % done 2901 iterations in 1.785s
% 2.06/2.25  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.06/2.25  % SZS output start Refutation
% 2.06/2.25  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 2.06/2.25  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.06/2.25  thf(sk_B_type, type, sk_B: $i > $i).
% 2.06/2.25  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.06/2.25  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.06/2.25  thf(sk_A_type, type, sk_A: $i).
% 2.06/2.25  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.06/2.25  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.06/2.25  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.06/2.25  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.06/2.25  thf(t79_xboole_1, conjecture,
% 2.06/2.25    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 2.06/2.25  thf(zf_stmt_0, negated_conjecture,
% 2.06/2.25    (~( ![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )),
% 2.06/2.25    inference('cnf.neg', [status(esa)], [t79_xboole_1])).
% 2.06/2.25  thf('0', plain, (~ (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B_1) @ sk_B_1)),
% 2.06/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.25  thf(d4_xboole_0, axiom,
% 2.06/2.25    (![A:$i,B:$i,C:$i]:
% 2.06/2.25     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 2.06/2.25       ( ![D:$i]:
% 2.06/2.25         ( ( r2_hidden @ D @ C ) <=>
% 2.06/2.25           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 2.06/2.25  thf('1', plain,
% 2.06/2.25      (![X6 : $i, X7 : $i, X10 : $i]:
% 2.06/2.25         (((X10) = (k3_xboole_0 @ X6 @ X7))
% 2.06/2.25          | (r2_hidden @ (sk_D @ X10 @ X7 @ X6) @ X6)
% 2.06/2.25          | (r2_hidden @ (sk_D @ X10 @ X7 @ X6) @ X10))),
% 2.06/2.25      inference('cnf', [status(esa)], [d4_xboole_0])).
% 2.06/2.25  thf(d1_xboole_0, axiom,
% 2.06/2.25    (![A:$i]:
% 2.06/2.25     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 2.06/2.25  thf('2', plain,
% 2.06/2.25      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 2.06/2.25      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.06/2.25  thf('3', plain,
% 2.06/2.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.06/2.25         ((r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X1)
% 2.06/2.25          | ((X0) = (k3_xboole_0 @ X1 @ X2))
% 2.06/2.25          | ~ (v1_xboole_0 @ X0))),
% 2.06/2.25      inference('sup-', [status(thm)], ['1', '2'])).
% 2.06/2.25  thf('4', plain,
% 2.06/2.25      (![X6 : $i, X7 : $i, X10 : $i]:
% 2.06/2.25         (((X10) = (k3_xboole_0 @ X6 @ X7))
% 2.06/2.25          | (r2_hidden @ (sk_D @ X10 @ X7 @ X6) @ X7)
% 2.06/2.25          | (r2_hidden @ (sk_D @ X10 @ X7 @ X6) @ X10))),
% 2.06/2.25      inference('cnf', [status(esa)], [d4_xboole_0])).
% 2.06/2.25  thf('5', plain,
% 2.06/2.25      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 2.06/2.25      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.06/2.25  thf(d5_xboole_0, axiom,
% 2.06/2.25    (![A:$i,B:$i,C:$i]:
% 2.06/2.25     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 2.06/2.25       ( ![D:$i]:
% 2.06/2.25         ( ( r2_hidden @ D @ C ) <=>
% 2.06/2.25           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 2.06/2.25  thf('6', plain,
% 2.06/2.25      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 2.06/2.25         (~ (r2_hidden @ X15 @ X14)
% 2.06/2.25          | (r2_hidden @ X15 @ X12)
% 2.06/2.25          | ((X14) != (k4_xboole_0 @ X12 @ X13)))),
% 2.06/2.25      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.06/2.25  thf('7', plain,
% 2.06/2.25      (![X12 : $i, X13 : $i, X15 : $i]:
% 2.06/2.25         ((r2_hidden @ X15 @ X12)
% 2.06/2.25          | ~ (r2_hidden @ X15 @ (k4_xboole_0 @ X12 @ X13)))),
% 2.06/2.25      inference('simplify', [status(thm)], ['6'])).
% 2.06/2.25  thf('8', plain,
% 2.06/2.25      (![X0 : $i, X1 : $i]:
% 2.06/2.25         ((v1_xboole_0 @ (k4_xboole_0 @ X1 @ X0))
% 2.06/2.25          | (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 2.06/2.25      inference('sup-', [status(thm)], ['5', '7'])).
% 2.06/2.25  thf('9', plain,
% 2.06/2.25      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 2.06/2.25      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.06/2.25  thf('10', plain,
% 2.06/2.25      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 2.06/2.25         (~ (r2_hidden @ X15 @ X14)
% 2.06/2.25          | ~ (r2_hidden @ X15 @ X13)
% 2.06/2.25          | ((X14) != (k4_xboole_0 @ X12 @ X13)))),
% 2.06/2.25      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.06/2.25  thf('11', plain,
% 2.06/2.25      (![X12 : $i, X13 : $i, X15 : $i]:
% 2.06/2.25         (~ (r2_hidden @ X15 @ X13)
% 2.06/2.25          | ~ (r2_hidden @ X15 @ (k4_xboole_0 @ X12 @ X13)))),
% 2.06/2.25      inference('simplify', [status(thm)], ['10'])).
% 2.06/2.25  thf('12', plain,
% 2.06/2.25      (![X0 : $i, X1 : $i]:
% 2.06/2.25         ((v1_xboole_0 @ (k4_xboole_0 @ X1 @ X0))
% 2.06/2.25          | ~ (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 2.06/2.25      inference('sup-', [status(thm)], ['9', '11'])).
% 2.06/2.25  thf('13', plain,
% 2.06/2.25      (![X0 : $i]:
% 2.06/2.25         ((v1_xboole_0 @ (k4_xboole_0 @ X0 @ X0))
% 2.06/2.25          | (v1_xboole_0 @ (k4_xboole_0 @ X0 @ X0)))),
% 2.06/2.25      inference('sup-', [status(thm)], ['8', '12'])).
% 2.06/2.25  thf('14', plain, (![X0 : $i]: (v1_xboole_0 @ (k4_xboole_0 @ X0 @ X0))),
% 2.06/2.25      inference('simplify', [status(thm)], ['13'])).
% 2.06/2.25  thf(t6_boole, axiom,
% 2.06/2.25    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 2.06/2.25  thf('15', plain,
% 2.06/2.25      (![X20 : $i]: (((X20) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X20))),
% 2.06/2.25      inference('cnf', [status(esa)], [t6_boole])).
% 2.06/2.25  thf('16', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.06/2.25      inference('sup-', [status(thm)], ['14', '15'])).
% 2.06/2.25  thf('17', plain,
% 2.06/2.25      (![X12 : $i, X13 : $i, X15 : $i]:
% 2.06/2.25         (~ (r2_hidden @ X15 @ X13)
% 2.06/2.25          | ~ (r2_hidden @ X15 @ (k4_xboole_0 @ X12 @ X13)))),
% 2.06/2.25      inference('simplify', [status(thm)], ['10'])).
% 2.06/2.25  thf('18', plain,
% 2.06/2.25      (![X0 : $i, X1 : $i]:
% 2.06/2.25         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 2.06/2.25      inference('sup-', [status(thm)], ['16', '17'])).
% 2.06/2.25  thf('19', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 2.06/2.25      inference('condensation', [status(thm)], ['18'])).
% 2.06/2.25  thf('20', plain,
% 2.06/2.25      (![X0 : $i, X1 : $i]:
% 2.06/2.25         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X1)
% 2.06/2.25          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ X1)))),
% 2.06/2.25      inference('sup-', [status(thm)], ['4', '19'])).
% 2.06/2.25  thf('21', plain,
% 2.06/2.25      (![X12 : $i, X13 : $i, X15 : $i]:
% 2.06/2.25         (~ (r2_hidden @ X15 @ X13)
% 2.06/2.25          | ~ (r2_hidden @ X15 @ (k4_xboole_0 @ X12 @ X13)))),
% 2.06/2.25      inference('simplify', [status(thm)], ['10'])).
% 2.06/2.25  thf('22', plain,
% 2.06/2.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.06/2.25         (((k1_xboole_0) = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 2.06/2.25          | ~ (r2_hidden @ 
% 2.06/2.25               (sk_D @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X0))),
% 2.06/2.25      inference('sup-', [status(thm)], ['20', '21'])).
% 2.06/2.25  thf('23', plain,
% 2.06/2.25      (![X0 : $i, X1 : $i]:
% 2.06/2.25         (~ (v1_xboole_0 @ k1_xboole_0)
% 2.06/2.25          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 2.06/2.25          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 2.06/2.25      inference('sup-', [status(thm)], ['3', '22'])).
% 2.06/2.25  thf('24', plain, (![X0 : $i]: (v1_xboole_0 @ (k4_xboole_0 @ X0 @ X0))),
% 2.06/2.25      inference('simplify', [status(thm)], ['13'])).
% 2.06/2.25  thf('25', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.06/2.25      inference('sup-', [status(thm)], ['14', '15'])).
% 2.06/2.25  thf('26', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.06/2.25      inference('demod', [status(thm)], ['24', '25'])).
% 2.06/2.25  thf('27', plain,
% 2.06/2.25      (![X0 : $i, X1 : $i]:
% 2.06/2.25         (((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 2.06/2.25          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 2.06/2.25      inference('demod', [status(thm)], ['23', '26'])).
% 2.06/2.25  thf('28', plain,
% 2.06/2.25      (![X0 : $i, X1 : $i]:
% 2.06/2.25         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.06/2.25      inference('simplify', [status(thm)], ['27'])).
% 2.06/2.25  thf(commutativity_k3_xboole_0, axiom,
% 2.06/2.25    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.06/2.25  thf('29', plain,
% 2.06/2.25      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.06/2.25      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.06/2.25  thf(d7_xboole_0, axiom,
% 2.06/2.25    (![A:$i,B:$i]:
% 2.06/2.25     ( ( r1_xboole_0 @ A @ B ) <=>
% 2.06/2.25       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 2.06/2.25  thf('30', plain,
% 2.06/2.25      (![X17 : $i, X19 : $i]:
% 2.06/2.25         ((r1_xboole_0 @ X17 @ X19)
% 2.06/2.25          | ((k3_xboole_0 @ X17 @ X19) != (k1_xboole_0)))),
% 2.06/2.25      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.06/2.25  thf('31', plain,
% 2.06/2.25      (![X0 : $i, X1 : $i]:
% 2.06/2.25         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 2.06/2.25      inference('sup-', [status(thm)], ['29', '30'])).
% 2.06/2.25  thf('32', plain,
% 2.06/2.25      (![X0 : $i, X1 : $i]:
% 2.06/2.25         (((k1_xboole_0) != (k1_xboole_0))
% 2.06/2.25          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 2.06/2.25      inference('sup-', [status(thm)], ['28', '31'])).
% 2.06/2.25  thf('33', plain,
% 2.06/2.25      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 2.06/2.25      inference('simplify', [status(thm)], ['32'])).
% 2.06/2.25  thf('34', plain, ($false), inference('demod', [status(thm)], ['0', '33'])).
% 2.06/2.25  
% 2.06/2.25  % SZS output end Refutation
% 2.06/2.25  
% 2.06/2.26  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
