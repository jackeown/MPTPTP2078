%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oB2MhqYZlG

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:27 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   45 (  46 expanded)
%              Number of leaves         :   23 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :  242 ( 245 expanded)
%              Number of equality atoms :   28 (  29 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t71_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_enumset1 @ A @ A @ B @ C )
        = ( k1_enumset1 @ A @ B @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t71_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k1_enumset1 @ X23 @ X24 @ X25 )
      = ( k2_xboole_0 @ ( k1_tarski @ X23 ) @ ( k2_tarski @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ X20 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('6',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('7',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ X20 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['4','7'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('10',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k1_tarski @ X2 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','13'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_xboole_0 @ X14 @ X13 )
        = X13 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('17',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k2_enumset1 @ X26 @ X27 @ X28 @ X29 )
      = ( k2_xboole_0 @ ( k1_tarski @ X26 ) @ ( k1_enumset1 @ X27 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','18'])).

thf('20',plain,(
    $false ),
    inference(simplify,[status(thm)],['19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oB2MhqYZlG
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:52:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.40/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.58  % Solved by: fo/fo7.sh
% 0.40/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.58  % done 223 iterations in 0.129s
% 0.40/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.58  % SZS output start Refutation
% 0.40/0.58  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.40/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.58  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.40/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.58  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.40/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.40/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.40/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.58  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.40/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.58  thf(t71_enumset1, conjecture,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.40/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.58    (~( ![A:$i,B:$i,C:$i]:
% 0.40/0.58        ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ) )),
% 0.40/0.58    inference('cnf.neg', [status(esa)], [t71_enumset1])).
% 0.40/0.58  thf('0', plain,
% 0.40/0.58      (((k2_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.40/0.58         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(t42_enumset1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.40/0.58       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.40/0.58  thf('1', plain,
% 0.40/0.58      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.40/0.58         ((k1_enumset1 @ X23 @ X24 @ X25)
% 0.40/0.58           = (k2_xboole_0 @ (k1_tarski @ X23) @ (k2_tarski @ X24 @ X25)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.40/0.58  thf(t21_xboole_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.40/0.58  thf('2', plain,
% 0.40/0.58      (![X18 : $i, X19 : $i]:
% 0.40/0.58         ((k3_xboole_0 @ X18 @ (k2_xboole_0 @ X18 @ X19)) = (X18))),
% 0.40/0.58      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.40/0.58  thf(t100_xboole_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.40/0.58  thf('3', plain,
% 0.40/0.58      (![X8 : $i, X9 : $i]:
% 0.40/0.58         ((k4_xboole_0 @ X8 @ X9)
% 0.40/0.58           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.40/0.58  thf('4', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.40/0.58           = (k5_xboole_0 @ X0 @ X0))),
% 0.40/0.58      inference('sup+', [status(thm)], ['2', '3'])).
% 0.40/0.58  thf(t92_xboole_1, axiom,
% 0.40/0.58    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.40/0.58  thf('5', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ X20) = (k1_xboole_0))),
% 0.40/0.58      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.40/0.58  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.40/0.58  thf('6', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.40/0.58      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.40/0.58  thf('7', plain,
% 0.40/0.58      (![X20 : $i]: ((k5_xboole_0 @ X20 @ X20) = (o_0_0_xboole_0))),
% 0.40/0.58      inference('demod', [status(thm)], ['5', '6'])).
% 0.40/0.58  thf('8', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) = (o_0_0_xboole_0))),
% 0.40/0.58      inference('demod', [status(thm)], ['4', '7'])).
% 0.40/0.58  thf(l32_xboole_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.40/0.58  thf('9', plain,
% 0.40/0.58      (![X5 : $i, X6 : $i]:
% 0.40/0.58         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 0.40/0.58      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.40/0.58  thf('10', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.40/0.58      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.40/0.58  thf('11', plain,
% 0.40/0.58      (![X5 : $i, X6 : $i]:
% 0.40/0.58         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (o_0_0_xboole_0)))),
% 0.40/0.58      inference('demod', [status(thm)], ['9', '10'])).
% 0.40/0.58  thf('12', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (((o_0_0_xboole_0) != (o_0_0_xboole_0))
% 0.40/0.58          | (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['8', '11'])).
% 0.40/0.58  thf('13', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.40/0.58      inference('simplify', [status(thm)], ['12'])).
% 0.40/0.58  thf('14', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.58         (r1_tarski @ (k1_tarski @ X2) @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.40/0.58      inference('sup+', [status(thm)], ['1', '13'])).
% 0.40/0.58  thf(t12_xboole_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.40/0.58  thf('15', plain,
% 0.40/0.58      (![X13 : $i, X14 : $i]:
% 0.40/0.58         (((k2_xboole_0 @ X14 @ X13) = (X13)) | ~ (r1_tarski @ X14 @ X13))),
% 0.40/0.58      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.40/0.58  thf('16', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.58         ((k2_xboole_0 @ (k1_tarski @ X2) @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.40/0.58           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['14', '15'])).
% 0.40/0.58  thf(t44_enumset1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.58     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.40/0.58       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.40/0.58  thf('17', plain,
% 0.40/0.58      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.40/0.58         ((k2_enumset1 @ X26 @ X27 @ X28 @ X29)
% 0.40/0.58           = (k2_xboole_0 @ (k1_tarski @ X26) @ (k1_enumset1 @ X27 @ X28 @ X29)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.40/0.58  thf('18', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.58         ((k2_enumset1 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.40/0.58      inference('demod', [status(thm)], ['16', '17'])).
% 0.40/0.58  thf('19', plain,
% 0.40/0.58      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.40/0.58         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.40/0.58      inference('demod', [status(thm)], ['0', '18'])).
% 0.40/0.58  thf('20', plain, ($false), inference('simplify', [status(thm)], ['19'])).
% 0.40/0.58  
% 0.40/0.58  % SZS output end Refutation
% 0.40/0.58  
% 0.42/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
