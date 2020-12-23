%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.klyzh3ze9o

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:47 EST 2020

% Result     : Theorem 29.11s
% Output     : Refutation 29.11s
% Verified   : 
% Statistics : Number of formulae       :   49 (  60 expanded)
%              Number of leaves         :   15 (  24 expanded)
%              Depth                    :   12
%              Number of atoms          :  297 ( 395 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ~ ( r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('2',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('4',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X9 @ X10 )
      | ( r1_xboole_0 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ sk_C @ X0 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_C @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t81_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('14',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X13 ) )
      | ~ ( r1_xboole_0 @ X12 @ ( k4_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t81_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X9 @ X10 )
      | ( r1_xboole_0 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r1_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('22',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('23',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) )
    = sk_A ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('25',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('27',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('28',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['25','30'])).

thf('32',plain,(
    $false ),
    inference(demod,[status(thm)],['0','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.klyzh3ze9o
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:31:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 29.11/29.40  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 29.11/29.40  % Solved by: fo/fo7.sh
% 29.11/29.40  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 29.11/29.40  % done 3071 iterations in 28.945s
% 29.11/29.40  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 29.11/29.40  % SZS output start Refutation
% 29.11/29.40  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 29.11/29.40  thf(sk_B_type, type, sk_B: $i).
% 29.11/29.40  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 29.11/29.40  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 29.11/29.40  thf(sk_A_type, type, sk_A: $i).
% 29.11/29.40  thf(sk_C_type, type, sk_C: $i).
% 29.11/29.40  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 29.11/29.40  thf(t86_xboole_1, conjecture,
% 29.11/29.40    (![A:$i,B:$i,C:$i]:
% 29.11/29.40     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 29.11/29.40       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 29.11/29.40  thf(zf_stmt_0, negated_conjecture,
% 29.11/29.40    (~( ![A:$i,B:$i,C:$i]:
% 29.11/29.40        ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 29.11/29.40          ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )),
% 29.11/29.40    inference('cnf.neg', [status(esa)], [t86_xboole_1])).
% 29.11/29.40  thf('0', plain, (~ (r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 29.11/29.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.11/29.40  thf(t48_xboole_1, axiom,
% 29.11/29.40    (![A:$i,B:$i]:
% 29.11/29.40     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 29.11/29.40  thf('1', plain,
% 29.11/29.40      (![X6 : $i, X7 : $i]:
% 29.11/29.40         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 29.11/29.40           = (k3_xboole_0 @ X6 @ X7))),
% 29.11/29.40      inference('cnf', [status(esa)], [t48_xboole_1])).
% 29.11/29.40  thf('2', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 29.11/29.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.11/29.40  thf(symmetry_r1_xboole_0, axiom,
% 29.11/29.40    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 29.11/29.40  thf('3', plain,
% 29.11/29.40      (![X2 : $i, X3 : $i]:
% 29.11/29.40         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 29.11/29.40      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 29.11/29.40  thf('4', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 29.11/29.40      inference('sup-', [status(thm)], ['2', '3'])).
% 29.11/29.40  thf(t36_xboole_1, axiom,
% 29.11/29.40    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 29.11/29.40  thf('5', plain,
% 29.11/29.40      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 29.11/29.40      inference('cnf', [status(esa)], [t36_xboole_1])).
% 29.11/29.40  thf(t63_xboole_1, axiom,
% 29.11/29.40    (![A:$i,B:$i,C:$i]:
% 29.11/29.40     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 29.11/29.40       ( r1_xboole_0 @ A @ C ) ))).
% 29.11/29.40  thf('6', plain,
% 29.11/29.40      (![X8 : $i, X9 : $i, X10 : $i]:
% 29.11/29.40         (~ (r1_tarski @ X8 @ X9)
% 29.11/29.40          | ~ (r1_xboole_0 @ X9 @ X10)
% 29.11/29.40          | (r1_xboole_0 @ X8 @ X10))),
% 29.11/29.40      inference('cnf', [status(esa)], [t63_xboole_1])).
% 29.11/29.40  thf('7', plain,
% 29.11/29.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.11/29.40         ((r1_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)
% 29.11/29.40          | ~ (r1_xboole_0 @ X0 @ X2))),
% 29.11/29.40      inference('sup-', [status(thm)], ['5', '6'])).
% 29.11/29.40  thf('8', plain,
% 29.11/29.40      (![X0 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ sk_C @ X0) @ sk_A)),
% 29.11/29.40      inference('sup-', [status(thm)], ['4', '7'])).
% 29.11/29.40  thf('9', plain,
% 29.11/29.40      (![X2 : $i, X3 : $i]:
% 29.11/29.40         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 29.11/29.40      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 29.11/29.40  thf('10', plain,
% 29.11/29.40      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_C @ X0))),
% 29.11/29.40      inference('sup-', [status(thm)], ['8', '9'])).
% 29.11/29.40  thf('11', plain,
% 29.11/29.40      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_C @ X0))),
% 29.11/29.40      inference('sup+', [status(thm)], ['1', '10'])).
% 29.11/29.40  thf(commutativity_k3_xboole_0, axiom,
% 29.11/29.40    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 29.11/29.40  thf('12', plain,
% 29.11/29.40      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 29.11/29.40      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 29.11/29.40  thf('13', plain,
% 29.11/29.40      (![X6 : $i, X7 : $i]:
% 29.11/29.40         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 29.11/29.40           = (k3_xboole_0 @ X6 @ X7))),
% 29.11/29.40      inference('cnf', [status(esa)], [t48_xboole_1])).
% 29.11/29.40  thf(t81_xboole_1, axiom,
% 29.11/29.40    (![A:$i,B:$i,C:$i]:
% 29.11/29.40     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 29.11/29.40       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 29.11/29.40  thf('14', plain,
% 29.11/29.40      (![X11 : $i, X12 : $i, X13 : $i]:
% 29.11/29.40         ((r1_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X13))
% 29.11/29.40          | ~ (r1_xboole_0 @ X12 @ (k4_xboole_0 @ X11 @ X13)))),
% 29.11/29.40      inference('cnf', [status(esa)], [t81_xboole_1])).
% 29.11/29.40  thf('15', plain,
% 29.11/29.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.11/29.40         (~ (r1_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 29.11/29.40          | (r1_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 29.11/29.40      inference('sup-', [status(thm)], ['13', '14'])).
% 29.11/29.40  thf('16', plain,
% 29.11/29.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.11/29.40         (~ (r1_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 29.11/29.40          | (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1))))),
% 29.11/29.40      inference('sup-', [status(thm)], ['12', '15'])).
% 29.11/29.40  thf('17', plain,
% 29.11/29.40      (![X0 : $i]:
% 29.11/29.40         (r1_xboole_0 @ X0 @ (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C)))),
% 29.11/29.40      inference('sup-', [status(thm)], ['11', '16'])).
% 29.11/29.40  thf('18', plain, ((r1_tarski @ sk_A @ sk_B)),
% 29.11/29.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.11/29.40  thf('19', plain,
% 29.11/29.40      (![X8 : $i, X9 : $i, X10 : $i]:
% 29.11/29.40         (~ (r1_tarski @ X8 @ X9)
% 29.11/29.40          | ~ (r1_xboole_0 @ X9 @ X10)
% 29.11/29.40          | (r1_xboole_0 @ X8 @ X10))),
% 29.11/29.40      inference('cnf', [status(esa)], [t63_xboole_1])).
% 29.11/29.40  thf('20', plain,
% 29.11/29.40      (![X0 : $i]: ((r1_xboole_0 @ sk_A @ X0) | ~ (r1_xboole_0 @ sk_B @ X0))),
% 29.11/29.40      inference('sup-', [status(thm)], ['18', '19'])).
% 29.11/29.40  thf('21', plain,
% 29.11/29.40      ((r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 29.11/29.40      inference('sup-', [status(thm)], ['17', '20'])).
% 29.11/29.40  thf(t83_xboole_1, axiom,
% 29.11/29.40    (![A:$i,B:$i]:
% 29.11/29.40     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 29.11/29.40  thf('22', plain,
% 29.11/29.40      (![X14 : $i, X15 : $i]:
% 29.11/29.40         (((k4_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_xboole_0 @ X14 @ X15))),
% 29.11/29.40      inference('cnf', [status(esa)], [t83_xboole_1])).
% 29.11/29.40  thf('23', plain,
% 29.11/29.40      (((k4_xboole_0 @ sk_A @ 
% 29.11/29.40         (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))) = (sk_A))),
% 29.11/29.40      inference('sup-', [status(thm)], ['21', '22'])).
% 29.11/29.40  thf('24', plain,
% 29.11/29.40      (![X6 : $i, X7 : $i]:
% 29.11/29.40         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 29.11/29.40           = (k3_xboole_0 @ X6 @ X7))),
% 29.11/29.40      inference('cnf', [status(esa)], [t48_xboole_1])).
% 29.11/29.40  thf('25', plain,
% 29.11/29.40      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 29.11/29.40      inference('demod', [status(thm)], ['23', '24'])).
% 29.11/29.40  thf('26', plain,
% 29.11/29.40      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 29.11/29.40      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 29.11/29.40  thf('27', plain,
% 29.11/29.40      (![X6 : $i, X7 : $i]:
% 29.11/29.40         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 29.11/29.40           = (k3_xboole_0 @ X6 @ X7))),
% 29.11/29.40      inference('cnf', [status(esa)], [t48_xboole_1])).
% 29.11/29.40  thf('28', plain,
% 29.11/29.40      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 29.11/29.40      inference('cnf', [status(esa)], [t36_xboole_1])).
% 29.11/29.40  thf('29', plain,
% 29.11/29.40      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 29.11/29.40      inference('sup+', [status(thm)], ['27', '28'])).
% 29.11/29.40  thf('30', plain,
% 29.11/29.40      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 29.11/29.40      inference('sup+', [status(thm)], ['26', '29'])).
% 29.11/29.40  thf('31', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 29.11/29.40      inference('sup+', [status(thm)], ['25', '30'])).
% 29.11/29.40  thf('32', plain, ($false), inference('demod', [status(thm)], ['0', '31'])).
% 29.11/29.40  
% 29.11/29.40  % SZS output end Refutation
% 29.11/29.40  
% 29.22/29.40  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
