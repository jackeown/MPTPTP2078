%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rDFyrYp71T

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:32 EST 2020

% Result     : Theorem 0.92s
% Output     : Refutation 0.92s
% Verified   : 
% Statistics : Number of formulae       :   50 (  64 expanded)
%              Number of leaves         :   18 (  27 expanded)
%              Depth                    :   13
%              Number of atoms          :  283 ( 394 expanded)
%              Number of equality atoms :   34 (  41 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
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
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
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
    r1_xboole_0 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('7',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','6'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k4_xboole_0 @ X20 @ X21 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_B ) )
    = sk_C ),
    inference('sup+',[status(thm)],['7','10'])).

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
    ! [X14: $i] :
      ( ( k2_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_B )
    = sk_C ),
    inference(demod,[status(thm)],['11','14'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C @ X0 )
      = ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C @ X0 )
      = ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['4','17'])).

thf('19',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_A )
    = ( k4_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['3','18'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('21',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_C @ sk_A ) )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('25',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('26',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['21','22','23','24','25'])).

thf('27',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('28',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['0','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rDFyrYp71T
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:46:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.92/1.10  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.92/1.10  % Solved by: fo/fo7.sh
% 0.92/1.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.92/1.10  % done 905 iterations in 0.653s
% 0.92/1.10  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.92/1.10  % SZS output start Refutation
% 0.92/1.10  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.92/1.10  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.92/1.10  thf(sk_A_type, type, sk_A: $i).
% 0.92/1.10  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.92/1.10  thf(sk_B_type, type, sk_B: $i).
% 0.92/1.10  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.92/1.10  thf(sk_C_type, type, sk_C: $i).
% 0.92/1.10  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.92/1.10  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.92/1.10  thf(t63_xboole_1, conjecture,
% 0.92/1.10    (![A:$i,B:$i,C:$i]:
% 0.92/1.10     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.92/1.10       ( r1_xboole_0 @ A @ C ) ))).
% 0.92/1.10  thf(zf_stmt_0, negated_conjecture,
% 0.92/1.10    (~( ![A:$i,B:$i,C:$i]:
% 0.92/1.10        ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.92/1.10          ( r1_xboole_0 @ A @ C ) ) )),
% 0.92/1.11    inference('cnf.neg', [status(esa)], [t63_xboole_1])).
% 0.92/1.11  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_C)),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf(t12_xboole_1, axiom,
% 0.92/1.11    (![A:$i,B:$i]:
% 0.92/1.11     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.92/1.11  thf('2', plain,
% 0.92/1.11      (![X12 : $i, X13 : $i]:
% 0.92/1.11         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 0.92/1.11      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.92/1.11  thf('3', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.92/1.11      inference('sup-', [status(thm)], ['1', '2'])).
% 0.92/1.11  thf(commutativity_k2_xboole_0, axiom,
% 0.92/1.11    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.92/1.11  thf('4', plain,
% 0.92/1.11      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.92/1.11      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.92/1.11  thf('5', plain, ((r1_xboole_0 @ sk_B @ sk_C)),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf(d7_xboole_0, axiom,
% 0.92/1.11    (![A:$i,B:$i]:
% 0.92/1.11     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.92/1.11       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.92/1.11  thf('6', plain,
% 0.92/1.11      (![X4 : $i, X5 : $i]:
% 0.92/1.11         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.92/1.11      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.92/1.11  thf('7', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))),
% 0.92/1.11      inference('sup-', [status(thm)], ['5', '6'])).
% 0.92/1.11  thf(commutativity_k3_xboole_0, axiom,
% 0.92/1.11    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.92/1.11  thf('8', plain,
% 0.92/1.11      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.92/1.11      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.92/1.11  thf(t51_xboole_1, axiom,
% 0.92/1.11    (![A:$i,B:$i]:
% 0.92/1.11     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.92/1.11       ( A ) ))).
% 0.92/1.11  thf('9', plain,
% 0.92/1.11      (![X20 : $i, X21 : $i]:
% 0.92/1.11         ((k2_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ (k4_xboole_0 @ X20 @ X21))
% 0.92/1.11           = (X20))),
% 0.92/1.11      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.92/1.11  thf('10', plain,
% 0.92/1.11      (![X0 : $i, X1 : $i]:
% 0.92/1.11         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.92/1.11           = (X0))),
% 0.92/1.11      inference('sup+', [status(thm)], ['8', '9'])).
% 0.92/1.11  thf('11', plain,
% 0.92/1.11      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_B)) = (sk_C))),
% 0.92/1.11      inference('sup+', [status(thm)], ['7', '10'])).
% 0.92/1.11  thf('12', plain,
% 0.92/1.11      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.92/1.11      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.92/1.11  thf(t1_boole, axiom,
% 0.92/1.11    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.92/1.11  thf('13', plain, (![X14 : $i]: ((k2_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.92/1.11      inference('cnf', [status(esa)], [t1_boole])).
% 0.92/1.11  thf('14', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.92/1.11      inference('sup+', [status(thm)], ['12', '13'])).
% 0.92/1.11  thf('15', plain, (((k4_xboole_0 @ sk_C @ sk_B) = (sk_C))),
% 0.92/1.11      inference('demod', [status(thm)], ['11', '14'])).
% 0.92/1.11  thf(t41_xboole_1, axiom,
% 0.92/1.11    (![A:$i,B:$i,C:$i]:
% 0.92/1.11     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.92/1.11       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.92/1.11  thf('16', plain,
% 0.92/1.11      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.92/1.11         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 0.92/1.11           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 0.92/1.11      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.92/1.11  thf('17', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         ((k4_xboole_0 @ sk_C @ X0)
% 0.92/1.11           = (k4_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.92/1.11      inference('sup+', [status(thm)], ['15', '16'])).
% 0.92/1.11  thf('18', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         ((k4_xboole_0 @ sk_C @ X0)
% 0.92/1.11           = (k4_xboole_0 @ sk_C @ (k2_xboole_0 @ X0 @ sk_B)))),
% 0.92/1.11      inference('sup+', [status(thm)], ['4', '17'])).
% 0.92/1.11  thf('19', plain,
% 0.92/1.11      (((k4_xboole_0 @ sk_C @ sk_A) = (k4_xboole_0 @ sk_C @ sk_B))),
% 0.92/1.11      inference('sup+', [status(thm)], ['3', '18'])).
% 0.92/1.11  thf(t48_xboole_1, axiom,
% 0.92/1.11    (![A:$i,B:$i]:
% 0.92/1.11     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.92/1.11  thf('20', plain,
% 0.92/1.11      (![X18 : $i, X19 : $i]:
% 0.92/1.11         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.92/1.11           = (k3_xboole_0 @ X18 @ X19))),
% 0.92/1.11      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.92/1.11  thf('21', plain,
% 0.92/1.11      (((k4_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_C @ sk_A))
% 0.92/1.11         = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.92/1.11      inference('sup+', [status(thm)], ['19', '20'])).
% 0.92/1.11  thf('22', plain,
% 0.92/1.11      (![X18 : $i, X19 : $i]:
% 0.92/1.11         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.92/1.11           = (k3_xboole_0 @ X18 @ X19))),
% 0.92/1.11      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.92/1.11  thf('23', plain,
% 0.92/1.11      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.92/1.11      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.92/1.11  thf('24', plain,
% 0.92/1.11      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.92/1.11      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.92/1.11  thf('25', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))),
% 0.92/1.11      inference('sup-', [status(thm)], ['5', '6'])).
% 0.92/1.11  thf('26', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.92/1.11      inference('demod', [status(thm)], ['21', '22', '23', '24', '25'])).
% 0.92/1.11  thf('27', plain,
% 0.92/1.11      (![X4 : $i, X6 : $i]:
% 0.92/1.11         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 0.92/1.11      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.92/1.11  thf('28', plain,
% 0.92/1.11      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_C))),
% 0.92/1.11      inference('sup-', [status(thm)], ['26', '27'])).
% 0.92/1.11  thf('29', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.92/1.11      inference('simplify', [status(thm)], ['28'])).
% 0.92/1.11  thf('30', plain, ($false), inference('demod', [status(thm)], ['0', '29'])).
% 0.92/1.11  
% 0.92/1.11  % SZS output end Refutation
% 0.92/1.11  
% 0.92/1.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
