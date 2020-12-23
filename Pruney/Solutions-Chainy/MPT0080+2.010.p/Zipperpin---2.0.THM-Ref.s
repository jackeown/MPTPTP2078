%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UQM4JsLNk2

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:05 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :   40 (  47 expanded)
%              Number of leaves         :   16 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :  224 ( 289 expanded)
%              Number of equality atoms :   23 (  26 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('6',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('8',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ ( k3_xboole_0 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_C ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13','16'])).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('19',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['3','17','18'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('20',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('21',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    $false ),
    inference(demod,[status(thm)],['0','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UQM4JsLNk2
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:15:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.70/0.89  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.70/0.89  % Solved by: fo/fo7.sh
% 0.70/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.70/0.89  % done 544 iterations in 0.437s
% 0.70/0.89  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.70/0.89  % SZS output start Refutation
% 0.70/0.89  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.70/0.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.70/0.89  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.70/0.89  thf(sk_B_type, type, sk_B: $i).
% 0.70/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.70/0.89  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.70/0.89  thf(sk_C_type, type, sk_C: $i).
% 0.70/0.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.70/0.89  thf(t73_xboole_1, conjecture,
% 0.70/0.89    (![A:$i,B:$i,C:$i]:
% 0.70/0.89     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.70/0.89       ( r1_tarski @ A @ B ) ))).
% 0.70/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.70/0.89    (~( ![A:$i,B:$i,C:$i]:
% 0.70/0.89        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 0.70/0.89            ( r1_xboole_0 @ A @ C ) ) =>
% 0.70/0.89          ( r1_tarski @ A @ B ) ) )),
% 0.70/0.89    inference('cnf.neg', [status(esa)], [t73_xboole_1])).
% 0.70/0.89  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('1', plain, ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf(t28_xboole_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.70/0.89  thf('2', plain,
% 0.70/0.89      (![X13 : $i, X14 : $i]:
% 0.70/0.89         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.70/0.89      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.70/0.89  thf('3', plain,
% 0.70/0.89      (((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.70/0.89      inference('sup-', [status(thm)], ['1', '2'])).
% 0.70/0.89  thf('4', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf(d7_xboole_0, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.70/0.89       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.70/0.89  thf('5', plain,
% 0.70/0.89      (![X4 : $i, X5 : $i]:
% 0.70/0.89         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.70/0.89      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.70/0.89  thf('6', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['4', '5'])).
% 0.70/0.89  thf(commutativity_k3_xboole_0, axiom,
% 0.70/0.89    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.70/0.89  thf('7', plain,
% 0.70/0.89      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.70/0.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.70/0.89  thf('8', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.70/0.89      inference('demod', [status(thm)], ['6', '7'])).
% 0.70/0.89  thf('9', plain,
% 0.70/0.89      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.70/0.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.70/0.89  thf(t23_xboole_1, axiom,
% 0.70/0.89    (![A:$i,B:$i,C:$i]:
% 0.70/0.89     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.70/0.89       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.70/0.89  thf('10', plain,
% 0.70/0.89      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.70/0.89         ((k3_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12))
% 0.70/0.89           = (k2_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ 
% 0.70/0.89              (k3_xboole_0 @ X10 @ X12)))),
% 0.70/0.89      inference('cnf', [status(esa)], [t23_xboole_1])).
% 0.70/0.89  thf('11', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.89         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1))
% 0.70/0.89           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.70/0.89      inference('sup+', [status(thm)], ['9', '10'])).
% 0.70/0.89  thf('12', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         ((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_C))
% 0.70/0.89           = (k2_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ k1_xboole_0))),
% 0.70/0.89      inference('sup+', [status(thm)], ['8', '11'])).
% 0.70/0.89  thf(commutativity_k2_xboole_0, axiom,
% 0.70/0.89    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.70/0.89  thf('13', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.70/0.89      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.70/0.89  thf('14', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.70/0.89      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.70/0.89  thf(t1_boole, axiom,
% 0.70/0.89    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.70/0.89  thf('15', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.70/0.89      inference('cnf', [status(esa)], [t1_boole])).
% 0.70/0.89  thf('16', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.70/0.89      inference('sup+', [status(thm)], ['14', '15'])).
% 0.70/0.89  thf('17', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         ((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_C))
% 0.70/0.89           = (k3_xboole_0 @ sk_A @ X0))),
% 0.70/0.89      inference('demod', [status(thm)], ['12', '13', '16'])).
% 0.70/0.89  thf('18', plain,
% 0.70/0.89      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.70/0.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.70/0.89  thf('19', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.70/0.89      inference('demod', [status(thm)], ['3', '17', '18'])).
% 0.70/0.89  thf(t17_xboole_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.70/0.89  thf('20', plain,
% 0.70/0.89      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 0.70/0.89      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.70/0.89  thf('21', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.70/0.89      inference('sup+', [status(thm)], ['19', '20'])).
% 0.70/0.89  thf('22', plain, ($false), inference('demod', [status(thm)], ['0', '21'])).
% 0.70/0.89  
% 0.70/0.89  % SZS output end Refutation
% 0.70/0.89  
% 0.70/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
