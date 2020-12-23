%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rldI5YbtB1

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:35 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :   50 (  66 expanded)
%              Number of leaves         :   18 (  27 expanded)
%              Depth                    :   15
%              Number of atoms          :  270 ( 388 expanded)
%              Number of equality atoms :   29 (  34 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t63_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_xboole_0 @ B @ C ) )
       => ( r1_xboole_0 @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t63_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('3',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('5',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('7',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('10',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ ( k4_xboole_0 @ X19 @ X20 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('11',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_C_1 @ sk_B ) )
    = sk_C_1 ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X13: $i] :
      ( ( k2_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_B )
    = sk_C_1 ),
    inference(demod,[status(thm)],['11','14'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C_1 @ X0 )
      = ( k4_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C_1 @ X0 )
      = ( k4_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['4','17'])).

thf('19',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_A )
    = ( k4_xboole_0 @ sk_C_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','18'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('21',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_C_1 @ sk_A ) )
    = ( k3_xboole_0 @ sk_C_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('23',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('24',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('26',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_A ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('29',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['0','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rldI5YbtB1
% 0.12/0.32  % Computer   : n020.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 11:56:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.55/0.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.55/0.78  % Solved by: fo/fo7.sh
% 0.55/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.78  % done 658 iterations in 0.351s
% 0.55/0.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.55/0.78  % SZS output start Refutation
% 0.55/0.78  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.55/0.78  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.55/0.78  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.55/0.78  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.55/0.78  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.55/0.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.55/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.78  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.55/0.78  thf(t63_xboole_1, conjecture,
% 0.55/0.78    (![A:$i,B:$i,C:$i]:
% 0.55/0.78     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.55/0.78       ( r1_xboole_0 @ A @ C ) ))).
% 0.55/0.78  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.78    (~( ![A:$i,B:$i,C:$i]:
% 0.55/0.78        ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.55/0.78          ( r1_xboole_0 @ A @ C ) ) )),
% 0.55/0.78    inference('cnf.neg', [status(esa)], [t63_xboole_1])).
% 0.55/0.78  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_C_1)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf(t12_xboole_1, axiom,
% 0.55/0.78    (![A:$i,B:$i]:
% 0.55/0.78     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.55/0.78  thf('2', plain,
% 0.55/0.78      (![X11 : $i, X12 : $i]:
% 0.55/0.78         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 0.55/0.78      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.55/0.78  thf('3', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.55/0.78      inference('sup-', [status(thm)], ['1', '2'])).
% 0.55/0.78  thf(commutativity_k2_xboole_0, axiom,
% 0.55/0.78    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.55/0.78  thf('4', plain,
% 0.55/0.78      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.55/0.78      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.55/0.78  thf('5', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf(symmetry_r1_xboole_0, axiom,
% 0.55/0.78    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.55/0.78  thf('6', plain,
% 0.55/0.78      (![X5 : $i, X6 : $i]:
% 0.55/0.78         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 0.55/0.78      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.55/0.78  thf('7', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 0.55/0.78      inference('sup-', [status(thm)], ['5', '6'])).
% 0.55/0.78  thf(d7_xboole_0, axiom,
% 0.55/0.78    (![A:$i,B:$i]:
% 0.55/0.78     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.55/0.78       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.55/0.78  thf('8', plain,
% 0.55/0.78      (![X2 : $i, X3 : $i]:
% 0.55/0.78         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.55/0.78      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.55/0.78  thf('9', plain, (((k3_xboole_0 @ sk_C_1 @ sk_B) = (k1_xboole_0))),
% 0.55/0.78      inference('sup-', [status(thm)], ['7', '8'])).
% 0.55/0.78  thf(t51_xboole_1, axiom,
% 0.55/0.78    (![A:$i,B:$i]:
% 0.55/0.78     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.55/0.78       ( A ) ))).
% 0.55/0.78  thf('10', plain,
% 0.55/0.78      (![X19 : $i, X20 : $i]:
% 0.55/0.78         ((k2_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ (k4_xboole_0 @ X19 @ X20))
% 0.55/0.78           = (X19))),
% 0.55/0.78      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.55/0.78  thf('11', plain,
% 0.55/0.78      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_C_1 @ sk_B)) = (sk_C_1))),
% 0.55/0.78      inference('sup+', [status(thm)], ['9', '10'])).
% 0.55/0.78  thf('12', plain,
% 0.55/0.78      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.55/0.78      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.55/0.78  thf(t1_boole, axiom,
% 0.55/0.78    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.55/0.78  thf('13', plain, (![X13 : $i]: ((k2_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.55/0.78      inference('cnf', [status(esa)], [t1_boole])).
% 0.55/0.78  thf('14', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.55/0.78      inference('sup+', [status(thm)], ['12', '13'])).
% 0.55/0.78  thf('15', plain, (((k4_xboole_0 @ sk_C_1 @ sk_B) = (sk_C_1))),
% 0.55/0.78      inference('demod', [status(thm)], ['11', '14'])).
% 0.55/0.78  thf(t41_xboole_1, axiom,
% 0.55/0.78    (![A:$i,B:$i,C:$i]:
% 0.55/0.78     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.55/0.78       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.55/0.78  thf('16', plain,
% 0.55/0.78      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.55/0.78         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.55/0.78           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.55/0.78      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.55/0.78  thf('17', plain,
% 0.55/0.78      (![X0 : $i]:
% 0.55/0.78         ((k4_xboole_0 @ sk_C_1 @ X0)
% 0.55/0.78           = (k4_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.55/0.78      inference('sup+', [status(thm)], ['15', '16'])).
% 0.55/0.78  thf('18', plain,
% 0.55/0.78      (![X0 : $i]:
% 0.55/0.78         ((k4_xboole_0 @ sk_C_1 @ X0)
% 0.55/0.78           = (k4_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ X0 @ sk_B)))),
% 0.55/0.78      inference('sup+', [status(thm)], ['4', '17'])).
% 0.55/0.78  thf('19', plain,
% 0.55/0.78      (((k4_xboole_0 @ sk_C_1 @ sk_A) = (k4_xboole_0 @ sk_C_1 @ sk_B))),
% 0.55/0.78      inference('sup+', [status(thm)], ['3', '18'])).
% 0.55/0.78  thf(t48_xboole_1, axiom,
% 0.55/0.78    (![A:$i,B:$i]:
% 0.55/0.78     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.55/0.78  thf('20', plain,
% 0.55/0.78      (![X17 : $i, X18 : $i]:
% 0.55/0.78         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.55/0.78           = (k3_xboole_0 @ X17 @ X18))),
% 0.55/0.78      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.55/0.78  thf('21', plain,
% 0.55/0.78      (((k4_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_C_1 @ sk_A))
% 0.55/0.78         = (k3_xboole_0 @ sk_C_1 @ sk_B))),
% 0.55/0.78      inference('sup+', [status(thm)], ['19', '20'])).
% 0.55/0.78  thf('22', plain,
% 0.55/0.78      (![X17 : $i, X18 : $i]:
% 0.55/0.78         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.55/0.78           = (k3_xboole_0 @ X17 @ X18))),
% 0.55/0.78      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.55/0.78  thf('23', plain, (((k3_xboole_0 @ sk_C_1 @ sk_B) = (k1_xboole_0))),
% 0.55/0.78      inference('sup-', [status(thm)], ['7', '8'])).
% 0.55/0.78  thf('24', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 0.55/0.78      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.55/0.78  thf('25', plain,
% 0.55/0.78      (![X2 : $i, X4 : $i]:
% 0.55/0.78         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.55/0.78      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.55/0.78  thf('26', plain,
% 0.55/0.78      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_C_1 @ sk_A))),
% 0.55/0.78      inference('sup-', [status(thm)], ['24', '25'])).
% 0.55/0.78  thf('27', plain, ((r1_xboole_0 @ sk_C_1 @ sk_A)),
% 0.55/0.78      inference('simplify', [status(thm)], ['26'])).
% 0.55/0.78  thf('28', plain,
% 0.55/0.78      (![X5 : $i, X6 : $i]:
% 0.55/0.78         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 0.55/0.78      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.55/0.78  thf('29', plain, ((r1_xboole_0 @ sk_A @ sk_C_1)),
% 0.55/0.78      inference('sup-', [status(thm)], ['27', '28'])).
% 0.55/0.78  thf('30', plain, ($false), inference('demod', [status(thm)], ['0', '29'])).
% 0.55/0.78  
% 0.55/0.78  % SZS output end Refutation
% 0.55/0.78  
% 0.62/0.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
