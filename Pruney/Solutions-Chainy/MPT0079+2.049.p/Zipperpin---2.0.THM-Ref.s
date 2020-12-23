%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.u0kuBp3xiz

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:03 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   58 (  80 expanded)
%              Number of leaves         :   21 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :  347 ( 586 expanded)
%              Number of equality atoms :   33 (  62 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('0',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('1',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X3 @ ( k2_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t72_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( ( k2_xboole_0 @ A @ B )
          = ( k2_xboole_0 @ C @ D ) )
        & ( r1_xboole_0 @ C @ A )
        & ( r1_xboole_0 @ D @ B ) )
     => ( C = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( ( k2_xboole_0 @ A @ B )
            = ( k2_xboole_0 @ C @ D ) )
          & ( r1_xboole_0 @ C @ A )
          & ( r1_xboole_0 @ D @ B ) )
       => ( C = B ) ) ),
    inference('cnf.neg',[status(esa)],[t72_xboole_1])).

thf('6',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      | ~ ( r1_tarski @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_A @ sk_B ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_B @ sk_C ) @ sk_D ),
    inference('sup-',[status(thm)],['5','8'])).

thf(t67_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ B @ C ) )
     => ( A = k1_xboole_0 ) ) )).

thf('10',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( X21 = k1_xboole_0 )
      | ~ ( r1_tarski @ X21 @ X22 )
      | ~ ( r1_tarski @ X21 @ X23 )
      | ~ ( r1_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t67_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_D @ X0 )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 )
      | ( ( k4_xboole_0 @ sk_B @ sk_C )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_tarski @ X24 @ ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('14',plain,(
    r1_tarski @ sk_C @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      | ~ ( r1_tarski @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('16',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_C @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t37_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X10: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X12 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('18',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = ( k4_xboole_0 @ B @ A ) )
     => ( A = B ) ) )).

thf('19',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X7 = X6 )
      | ( ( k4_xboole_0 @ X7 @ X6 )
       != ( k4_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t32_xboole_1])).

thf('20',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_C @ sk_A ) )
     != k1_xboole_0 )
    | ( sk_B
      = ( k4_xboole_0 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('23',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('25',plain,
    ( ( k4_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('27',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('29',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_C )
     != k1_xboole_0 )
    | ( sk_B = sk_C ) ),
    inference(demod,[status(thm)],['20','27','28'])).

thf('30',plain,(
    sk_C != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ( k4_xboole_0 @ sk_B @ sk_C )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_D @ X0 )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['11','31'])).

thf('33',plain,(
    ~ ( r1_xboole_0 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['0','32'])).

thf('34',plain,(
    r1_xboole_0 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['33','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.u0kuBp3xiz
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:42:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.36  % Running in FO mode
% 0.39/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.62  % Solved by: fo/fo7.sh
% 0.39/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.62  % done 533 iterations in 0.156s
% 0.39/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.62  % SZS output start Refutation
% 0.39/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.62  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.39/0.62  thf(sk_D_type, type, sk_D: $i).
% 0.39/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.39/0.62  thf(t36_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.39/0.62  thf('0', plain,
% 0.39/0.62      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 0.39/0.62      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.39/0.62  thf(t3_boole, axiom,
% 0.39/0.62    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.39/0.62  thf('1', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.39/0.62      inference('cnf', [status(esa)], [t3_boole])).
% 0.39/0.62  thf('2', plain,
% 0.39/0.62      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 0.39/0.62      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.39/0.62  thf('3', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.39/0.62      inference('sup+', [status(thm)], ['1', '2'])).
% 0.39/0.62  thf(t10_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.39/0.62  thf('4', plain,
% 0.39/0.62      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.39/0.62         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ X3 @ (k2_xboole_0 @ X5 @ X4)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.39/0.62  thf('5', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['3', '4'])).
% 0.39/0.62  thf(t72_xboole_1, conjecture,
% 0.39/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.62     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.39/0.62         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.39/0.62       ( ( C ) = ( B ) ) ))).
% 0.39/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.62    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.62        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.39/0.62            ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.39/0.62          ( ( C ) = ( B ) ) ) )),
% 0.39/0.62    inference('cnf.neg', [status(esa)], [t72_xboole_1])).
% 0.39/0.62  thf('6', plain,
% 0.39/0.62      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(t43_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.39/0.62       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.39/0.62  thf('7', plain,
% 0.39/0.62      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.39/0.62         ((r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.39/0.62          | ~ (r1_tarski @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.39/0.62  thf('8', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_A @ sk_B))
% 0.39/0.62          | (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C) @ sk_D))),
% 0.39/0.62      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.62  thf('9', plain, ((r1_tarski @ (k4_xboole_0 @ sk_B @ sk_C) @ sk_D)),
% 0.39/0.62      inference('sup-', [status(thm)], ['5', '8'])).
% 0.39/0.62  thf(t67_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 0.39/0.62         ( r1_xboole_0 @ B @ C ) ) =>
% 0.39/0.62       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.39/0.62  thf('10', plain,
% 0.39/0.62      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.39/0.62         (((X21) = (k1_xboole_0))
% 0.39/0.62          | ~ (r1_tarski @ X21 @ X22)
% 0.39/0.62          | ~ (r1_tarski @ X21 @ X23)
% 0.39/0.62          | ~ (r1_xboole_0 @ X22 @ X23))),
% 0.39/0.62      inference('cnf', [status(esa)], [t67_xboole_1])).
% 0.39/0.62  thf('11', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (r1_xboole_0 @ sk_D @ X0)
% 0.39/0.62          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ sk_C) @ X0)
% 0.39/0.62          | ((k4_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['9', '10'])).
% 0.39/0.62  thf('12', plain,
% 0.39/0.62      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(t7_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.39/0.62  thf('13', plain,
% 0.39/0.62      (![X24 : $i, X25 : $i]: (r1_tarski @ X24 @ (k2_xboole_0 @ X24 @ X25))),
% 0.39/0.62      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.39/0.62  thf('14', plain, ((r1_tarski @ sk_C @ (k2_xboole_0 @ sk_A @ sk_B))),
% 0.39/0.62      inference('sup+', [status(thm)], ['12', '13'])).
% 0.39/0.62  thf('15', plain,
% 0.39/0.62      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.39/0.62         ((r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.39/0.62          | ~ (r1_tarski @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.39/0.62  thf('16', plain, ((r1_tarski @ (k4_xboole_0 @ sk_C @ sk_A) @ sk_B)),
% 0.39/0.62      inference('sup-', [status(thm)], ['14', '15'])).
% 0.39/0.62  thf(t37_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.39/0.62  thf('17', plain,
% 0.39/0.62      (![X10 : $i, X12 : $i]:
% 0.39/0.62         (((k4_xboole_0 @ X10 @ X12) = (k1_xboole_0))
% 0.39/0.62          | ~ (r1_tarski @ X10 @ X12))),
% 0.39/0.62      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.39/0.62  thf('18', plain,
% 0.39/0.62      (((k4_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['16', '17'])).
% 0.39/0.62  thf(t32_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( ( k4_xboole_0 @ A @ B ) = ( k4_xboole_0 @ B @ A ) ) =>
% 0.39/0.62       ( ( A ) = ( B ) ) ))).
% 0.39/0.62  thf('19', plain,
% 0.39/0.62      (![X6 : $i, X7 : $i]:
% 0.39/0.62         (((X7) = (X6)) | ((k4_xboole_0 @ X7 @ X6) != (k4_xboole_0 @ X6 @ X7)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t32_xboole_1])).
% 0.39/0.62  thf('20', plain,
% 0.39/0.62      ((((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_C @ sk_A)) != (k1_xboole_0))
% 0.39/0.62        | ((sk_B) = (k4_xboole_0 @ sk_C @ sk_A)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['18', '19'])).
% 0.39/0.62  thf('21', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(d7_xboole_0, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.39/0.62       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.39/0.62  thf('22', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.39/0.62      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.39/0.62  thf('23', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['21', '22'])).
% 0.39/0.62  thf(t47_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.39/0.62  thf('24', plain,
% 0.39/0.62      (![X17 : $i, X18 : $i]:
% 0.39/0.62         ((k4_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18))
% 0.39/0.62           = (k4_xboole_0 @ X17 @ X18))),
% 0.39/0.62      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.39/0.62  thf('25', plain,
% 0.39/0.62      (((k4_xboole_0 @ sk_C @ k1_xboole_0) = (k4_xboole_0 @ sk_C @ sk_A))),
% 0.39/0.62      inference('sup+', [status(thm)], ['23', '24'])).
% 0.39/0.62  thf('26', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.39/0.62      inference('cnf', [status(esa)], [t3_boole])).
% 0.39/0.62  thf('27', plain, (((sk_C) = (k4_xboole_0 @ sk_C @ sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['25', '26'])).
% 0.39/0.62  thf('28', plain, (((sk_C) = (k4_xboole_0 @ sk_C @ sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['25', '26'])).
% 0.39/0.62  thf('29', plain,
% 0.39/0.62      ((((k4_xboole_0 @ sk_B @ sk_C) != (k1_xboole_0)) | ((sk_B) = (sk_C)))),
% 0.39/0.62      inference('demod', [status(thm)], ['20', '27', '28'])).
% 0.39/0.62  thf('30', plain, (((sk_C) != (sk_B))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('31', plain, (((k4_xboole_0 @ sk_B @ sk_C) != (k1_xboole_0))),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.39/0.62  thf('32', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (r1_xboole_0 @ sk_D @ X0)
% 0.39/0.62          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ sk_C) @ X0))),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['11', '31'])).
% 0.39/0.62  thf('33', plain, (~ (r1_xboole_0 @ sk_D @ sk_B)),
% 0.39/0.62      inference('sup-', [status(thm)], ['0', '32'])).
% 0.39/0.62  thf('34', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('35', plain, ($false), inference('demod', [status(thm)], ['33', '34'])).
% 0.39/0.62  
% 0.39/0.62  % SZS output end Refutation
% 0.39/0.62  
% 0.39/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
