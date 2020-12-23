%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FutF0dCEoL

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:51 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :   50 (  68 expanded)
%              Number of leaves         :   16 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :  311 ( 497 expanded)
%              Number of equality atoms :   11 (  16 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t114_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ A @ D )
        & ( r1_xboole_0 @ B @ D )
        & ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) @ D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_xboole_0 @ A @ D )
          & ( r1_xboole_0 @ B @ D )
          & ( r1_xboole_0 @ C @ D ) )
       => ( r1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) @ D ) ) ),
    inference('cnf.neg',[status(esa)],[t114_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_C ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_A @ sk_B ) ) @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('4',plain,(
    r1_xboole_0 @ sk_B @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

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
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_D ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_D ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf('10',plain,(
    r1_xboole_0 @ sk_A @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('12',plain,(
    r1_xboole_0 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t78_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ A @ C ) ) ) )).

thf('13',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_xboole_0 @ X13 @ X14 )
      | ( ( k3_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) )
        = ( k3_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t78_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t75_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) )).

thf('16',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t75_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_D @ X0 ) @ sk_D )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_D ),
    inference('sup-',[status(thm)],['9','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ X0 ) @ sk_D ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('23',plain,(
    r1_xboole_0 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('25',plain,(
    r1_xboole_0 @ sk_D @ sk_C ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_xboole_0 @ X13 @ X14 )
      | ( ( k3_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) )
        = ( k3_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t78_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_C @ X0 ) )
      = ( k3_xboole_0 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_D @ X0 ) @ sk_D )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_C @ X0 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_D ) @ sk_D )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_C @ X0 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf('31',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_A @ sk_B ) ) @ sk_D ),
    inference('sup-',[status(thm)],['21','30'])).

thf('32',plain,(
    $false ),
    inference(demod,[status(thm)],['2','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FutF0dCEoL
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:09:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.49/0.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.49/0.70  % Solved by: fo/fo7.sh
% 0.49/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.70  % done 612 iterations in 0.255s
% 0.49/0.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.49/0.70  % SZS output start Refutation
% 0.49/0.70  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.49/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.49/0.70  thf(sk_C_type, type, sk_C: $i).
% 0.49/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.70  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.49/0.70  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.49/0.70  thf(sk_D_type, type, sk_D: $i).
% 0.49/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.49/0.70  thf(t114_xboole_1, conjecture,
% 0.49/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.49/0.70     ( ( ( r1_xboole_0 @ A @ D ) & ( r1_xboole_0 @ B @ D ) & 
% 0.49/0.70         ( r1_xboole_0 @ C @ D ) ) =>
% 0.49/0.70       ( r1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) @ D ) ))).
% 0.49/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.70    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.49/0.70        ( ( ( r1_xboole_0 @ A @ D ) & ( r1_xboole_0 @ B @ D ) & 
% 0.49/0.70            ( r1_xboole_0 @ C @ D ) ) =>
% 0.49/0.70          ( r1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) @ D ) ) )),
% 0.49/0.70    inference('cnf.neg', [status(esa)], [t114_xboole_1])).
% 0.49/0.70  thf('0', plain,
% 0.49/0.70      (~ (r1_xboole_0 @ (k2_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_C) @ 
% 0.49/0.70          sk_D)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf(commutativity_k2_xboole_0, axiom,
% 0.49/0.70    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.49/0.70  thf('1', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.49/0.70      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.49/0.70  thf('2', plain,
% 0.49/0.70      (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_A @ sk_B)) @ 
% 0.49/0.70          sk_D)),
% 0.49/0.70      inference('demod', [status(thm)], ['0', '1'])).
% 0.49/0.70  thf(commutativity_k3_xboole_0, axiom,
% 0.49/0.70    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.49/0.70  thf('3', plain,
% 0.49/0.70      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.49/0.70      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.49/0.70  thf('4', plain, ((r1_xboole_0 @ sk_B @ sk_D)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf(t17_xboole_1, axiom,
% 0.49/0.70    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.49/0.70  thf('5', plain,
% 0.49/0.70      (![X6 : $i, X7 : $i]: (r1_tarski @ (k3_xboole_0 @ X6 @ X7) @ X6)),
% 0.49/0.70      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.49/0.70  thf(t63_xboole_1, axiom,
% 0.49/0.70    (![A:$i,B:$i,C:$i]:
% 0.49/0.70     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.49/0.70       ( r1_xboole_0 @ A @ C ) ))).
% 0.49/0.70  thf('6', plain,
% 0.49/0.70      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.49/0.70         (~ (r1_tarski @ X8 @ X9)
% 0.49/0.70          | ~ (r1_xboole_0 @ X9 @ X10)
% 0.49/0.70          | (r1_xboole_0 @ X8 @ X10))),
% 0.49/0.70      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.49/0.70  thf('7', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.70         ((r1_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2)
% 0.49/0.70          | ~ (r1_xboole_0 @ X0 @ X2))),
% 0.49/0.70      inference('sup-', [status(thm)], ['5', '6'])).
% 0.49/0.70  thf('8', plain,
% 0.49/0.70      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ X0) @ sk_D)),
% 0.49/0.70      inference('sup-', [status(thm)], ['4', '7'])).
% 0.49/0.70  thf('9', plain,
% 0.49/0.70      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ X0 @ sk_B) @ sk_D)),
% 0.49/0.70      inference('sup+', [status(thm)], ['3', '8'])).
% 0.49/0.70  thf('10', plain, ((r1_xboole_0 @ sk_A @ sk_D)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf(symmetry_r1_xboole_0, axiom,
% 0.49/0.70    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.49/0.70  thf('11', plain,
% 0.49/0.70      (![X4 : $i, X5 : $i]:
% 0.49/0.70         ((r1_xboole_0 @ X4 @ X5) | ~ (r1_xboole_0 @ X5 @ X4))),
% 0.49/0.70      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.49/0.70  thf('12', plain, ((r1_xboole_0 @ sk_D @ sk_A)),
% 0.49/0.70      inference('sup-', [status(thm)], ['10', '11'])).
% 0.49/0.70  thf(t78_xboole_1, axiom,
% 0.49/0.70    (![A:$i,B:$i,C:$i]:
% 0.49/0.70     ( ( r1_xboole_0 @ A @ B ) =>
% 0.49/0.70       ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.49/0.70         ( k3_xboole_0 @ A @ C ) ) ))).
% 0.49/0.70  thf('13', plain,
% 0.49/0.70      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.49/0.70         (~ (r1_xboole_0 @ X13 @ X14)
% 0.49/0.70          | ((k3_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15))
% 0.49/0.70              = (k3_xboole_0 @ X13 @ X15)))),
% 0.49/0.70      inference('cnf', [status(esa)], [t78_xboole_1])).
% 0.49/0.70  thf('14', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         ((k3_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_A @ X0))
% 0.49/0.70           = (k3_xboole_0 @ sk_D @ X0))),
% 0.49/0.70      inference('sup-', [status(thm)], ['12', '13'])).
% 0.49/0.70  thf('15', plain,
% 0.49/0.70      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.49/0.70      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.49/0.70  thf(t75_xboole_1, axiom,
% 0.49/0.70    (![A:$i,B:$i]:
% 0.49/0.70     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.49/0.70          ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) ))).
% 0.49/0.70  thf('16', plain,
% 0.49/0.70      (![X11 : $i, X12 : $i]:
% 0.49/0.70         ((r1_xboole_0 @ X11 @ X12)
% 0.49/0.70          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X12))),
% 0.49/0.70      inference('cnf', [status(esa)], [t75_xboole_1])).
% 0.49/0.70  thf('17', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         (~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 0.49/0.70          | (r1_xboole_0 @ X0 @ X1))),
% 0.49/0.70      inference('sup-', [status(thm)], ['15', '16'])).
% 0.49/0.70  thf('18', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         (~ (r1_xboole_0 @ (k3_xboole_0 @ sk_D @ X0) @ sk_D)
% 0.49/0.70          | (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ X0) @ sk_D))),
% 0.49/0.70      inference('sup-', [status(thm)], ['14', '17'])).
% 0.49/0.70  thf('19', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_D)),
% 0.49/0.70      inference('sup-', [status(thm)], ['9', '18'])).
% 0.49/0.70  thf('20', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.70         ((r1_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2)
% 0.49/0.70          | ~ (r1_xboole_0 @ X0 @ X2))),
% 0.49/0.70      inference('sup-', [status(thm)], ['5', '6'])).
% 0.49/0.70  thf('21', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         (r1_xboole_0 @ (k3_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ X0) @ sk_D)),
% 0.49/0.70      inference('sup-', [status(thm)], ['19', '20'])).
% 0.49/0.70  thf('22', plain,
% 0.49/0.70      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.49/0.70      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.49/0.70  thf('23', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('24', plain,
% 0.49/0.70      (![X4 : $i, X5 : $i]:
% 0.49/0.70         ((r1_xboole_0 @ X4 @ X5) | ~ (r1_xboole_0 @ X5 @ X4))),
% 0.49/0.70      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.49/0.70  thf('25', plain, ((r1_xboole_0 @ sk_D @ sk_C)),
% 0.49/0.70      inference('sup-', [status(thm)], ['23', '24'])).
% 0.49/0.70  thf('26', plain,
% 0.49/0.70      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.49/0.70         (~ (r1_xboole_0 @ X13 @ X14)
% 0.49/0.70          | ((k3_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15))
% 0.49/0.70              = (k3_xboole_0 @ X13 @ X15)))),
% 0.49/0.70      inference('cnf', [status(esa)], [t78_xboole_1])).
% 0.49/0.70  thf('27', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         ((k3_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_C @ X0))
% 0.49/0.70           = (k3_xboole_0 @ sk_D @ X0))),
% 0.49/0.70      inference('sup-', [status(thm)], ['25', '26'])).
% 0.49/0.70  thf('28', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         (~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 0.49/0.70          | (r1_xboole_0 @ X0 @ X1))),
% 0.49/0.70      inference('sup-', [status(thm)], ['15', '16'])).
% 0.49/0.70  thf('29', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         (~ (r1_xboole_0 @ (k3_xboole_0 @ sk_D @ X0) @ sk_D)
% 0.49/0.70          | (r1_xboole_0 @ (k2_xboole_0 @ sk_C @ X0) @ sk_D))),
% 0.49/0.70      inference('sup-', [status(thm)], ['27', '28'])).
% 0.49/0.70  thf('30', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         (~ (r1_xboole_0 @ (k3_xboole_0 @ X0 @ sk_D) @ sk_D)
% 0.49/0.70          | (r1_xboole_0 @ (k2_xboole_0 @ sk_C @ X0) @ sk_D))),
% 0.49/0.70      inference('sup-', [status(thm)], ['22', '29'])).
% 0.49/0.70  thf('31', plain,
% 0.49/0.70      ((r1_xboole_0 @ (k2_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_A @ sk_B)) @ sk_D)),
% 0.49/0.70      inference('sup-', [status(thm)], ['21', '30'])).
% 0.49/0.70  thf('32', plain, ($false), inference('demod', [status(thm)], ['2', '31'])).
% 0.49/0.70  
% 0.49/0.70  % SZS output end Refutation
% 0.49/0.70  
% 0.49/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
