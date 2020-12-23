%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H40P0SIvV4

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:50 EST 2020

% Result     : Theorem 16.02s
% Output     : Refutation 16.02s
% Verified   : 
% Statistics : Number of formulae       :   43 (  67 expanded)
%              Number of leaves         :   14 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :  344 ( 550 expanded)
%              Number of equality atoms :   33 (  55 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t111_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
        = ( k3_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t111_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_C @ sk_B ) )
 != ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('4',plain,(
    ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k3_xboole_0 @ sk_B @ sk_C ) )
 != ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','1','2','3'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('6',plain,(
    ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) )
 != ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k3_xboole_0 @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k3_xboole_0 @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('24',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','22','23','24'])).

thf('26',plain,(
    ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) )
 != ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['6','25'])).

thf('27',plain,(
    $false ),
    inference(simplify,[status(thm)],['26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H40P0SIvV4
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:11:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 16.02/16.28  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 16.02/16.28  % Solved by: fo/fo7.sh
% 16.02/16.28  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 16.02/16.28  % done 4855 iterations in 15.820s
% 16.02/16.28  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 16.02/16.28  % SZS output start Refutation
% 16.02/16.28  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 16.02/16.28  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 16.02/16.28  thf(sk_B_type, type, sk_B: $i).
% 16.02/16.28  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 16.02/16.28  thf(sk_A_type, type, sk_A: $i).
% 16.02/16.28  thf(sk_C_type, type, sk_C: $i).
% 16.02/16.28  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 16.02/16.28  thf(t111_xboole_1, conjecture,
% 16.02/16.28    (![A:$i,B:$i,C:$i]:
% 16.02/16.28     ( ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 16.02/16.28       ( k3_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 16.02/16.28  thf(zf_stmt_0, negated_conjecture,
% 16.02/16.28    (~( ![A:$i,B:$i,C:$i]:
% 16.02/16.28        ( ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 16.02/16.28          ( k3_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ B ) ) )),
% 16.02/16.28    inference('cnf.neg', [status(esa)], [t111_xboole_1])).
% 16.02/16.28  thf('0', plain,
% 16.02/16.28      (((k4_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 16.02/16.28         (k3_xboole_0 @ sk_C @ sk_B))
% 16.02/16.28         != (k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B))),
% 16.02/16.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.02/16.28  thf(commutativity_k3_xboole_0, axiom,
% 16.02/16.28    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 16.02/16.28  thf('1', plain,
% 16.02/16.28      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 16.02/16.28      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 16.02/16.28  thf('2', plain,
% 16.02/16.28      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 16.02/16.28      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 16.02/16.28  thf('3', plain,
% 16.02/16.28      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 16.02/16.28      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 16.02/16.28  thf('4', plain,
% 16.02/16.28      (((k4_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ 
% 16.02/16.28         (k3_xboole_0 @ sk_B @ sk_C))
% 16.02/16.28         != (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 16.02/16.28      inference('demod', [status(thm)], ['0', '1', '2', '3'])).
% 16.02/16.28  thf(t49_xboole_1, axiom,
% 16.02/16.28    (![A:$i,B:$i,C:$i]:
% 16.02/16.28     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 16.02/16.28       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 16.02/16.28  thf('5', plain,
% 16.02/16.28      (![X16 : $i, X17 : $i, X18 : $i]:
% 16.02/16.28         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 16.02/16.28           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 16.02/16.28      inference('cnf', [status(esa)], [t49_xboole_1])).
% 16.02/16.28  thf('6', plain,
% 16.02/16.28      (((k3_xboole_0 @ sk_B @ 
% 16.02/16.28         (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))
% 16.02/16.28         != (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 16.02/16.28      inference('demod', [status(thm)], ['4', '5'])).
% 16.02/16.28  thf('7', plain,
% 16.02/16.28      (![X16 : $i, X17 : $i, X18 : $i]:
% 16.02/16.28         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 16.02/16.28           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 16.02/16.28      inference('cnf', [status(esa)], [t49_xboole_1])).
% 16.02/16.28  thf('8', plain,
% 16.02/16.28      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 16.02/16.28      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 16.02/16.28  thf(t17_xboole_1, axiom,
% 16.02/16.28    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 16.02/16.28  thf('9', plain,
% 16.02/16.28      (![X12 : $i, X13 : $i]: (r1_tarski @ (k3_xboole_0 @ X12 @ X13) @ X12)),
% 16.02/16.28      inference('cnf', [status(esa)], [t17_xboole_1])).
% 16.02/16.28  thf(t28_xboole_1, axiom,
% 16.02/16.28    (![A:$i,B:$i]:
% 16.02/16.28     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 16.02/16.28  thf('10', plain,
% 16.02/16.28      (![X14 : $i, X15 : $i]:
% 16.02/16.28         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 16.02/16.28      inference('cnf', [status(esa)], [t28_xboole_1])).
% 16.02/16.28  thf('11', plain,
% 16.02/16.28      (![X0 : $i, X1 : $i]:
% 16.02/16.28         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 16.02/16.28           = (k3_xboole_0 @ X0 @ X1))),
% 16.02/16.28      inference('sup-', [status(thm)], ['9', '10'])).
% 16.02/16.28  thf(t16_xboole_1, axiom,
% 16.02/16.28    (![A:$i,B:$i,C:$i]:
% 16.02/16.28     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 16.02/16.28       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 16.02/16.28  thf('12', plain,
% 16.02/16.28      (![X9 : $i, X10 : $i, X11 : $i]:
% 16.02/16.28         ((k3_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11)
% 16.02/16.28           = (k3_xboole_0 @ X9 @ (k3_xboole_0 @ X10 @ X11)))),
% 16.02/16.28      inference('cnf', [status(esa)], [t16_xboole_1])).
% 16.02/16.28  thf('13', plain,
% 16.02/16.28      (![X0 : $i, X1 : $i]:
% 16.02/16.28         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 16.02/16.28           = (k3_xboole_0 @ X0 @ X1))),
% 16.02/16.28      inference('demod', [status(thm)], ['11', '12'])).
% 16.02/16.28  thf('14', plain,
% 16.02/16.28      (![X0 : $i, X1 : $i]:
% 16.02/16.28         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 16.02/16.28           = (k3_xboole_0 @ X1 @ X0))),
% 16.02/16.28      inference('sup+', [status(thm)], ['8', '13'])).
% 16.02/16.28  thf(t100_xboole_1, axiom,
% 16.02/16.28    (![A:$i,B:$i]:
% 16.02/16.28     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 16.02/16.28  thf('15', plain,
% 16.02/16.28      (![X7 : $i, X8 : $i]:
% 16.02/16.28         ((k4_xboole_0 @ X7 @ X8)
% 16.02/16.28           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 16.02/16.28      inference('cnf', [status(esa)], [t100_xboole_1])).
% 16.02/16.28  thf('16', plain,
% 16.02/16.28      (![X0 : $i, X1 : $i]:
% 16.02/16.28         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 16.02/16.28           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 16.02/16.28      inference('sup+', [status(thm)], ['14', '15'])).
% 16.02/16.28  thf('17', plain,
% 16.02/16.28      (![X7 : $i, X8 : $i]:
% 16.02/16.28         ((k4_xboole_0 @ X7 @ X8)
% 16.02/16.28           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 16.02/16.28      inference('cnf', [status(esa)], [t100_xboole_1])).
% 16.02/16.28  thf('18', plain,
% 16.02/16.28      (![X0 : $i, X1 : $i]:
% 16.02/16.28         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 16.02/16.28           = (k4_xboole_0 @ X1 @ X0))),
% 16.02/16.28      inference('demod', [status(thm)], ['16', '17'])).
% 16.02/16.28  thf('19', plain,
% 16.02/16.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.02/16.28         ((k3_xboole_0 @ X2 @ 
% 16.02/16.28           (k4_xboole_0 @ X1 @ (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)))
% 16.02/16.28           = (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 16.02/16.28      inference('sup+', [status(thm)], ['7', '18'])).
% 16.02/16.28  thf('20', plain,
% 16.02/16.28      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 16.02/16.28      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 16.02/16.28  thf('21', plain,
% 16.02/16.28      (![X9 : $i, X10 : $i, X11 : $i]:
% 16.02/16.28         ((k3_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11)
% 16.02/16.28           = (k3_xboole_0 @ X9 @ (k3_xboole_0 @ X10 @ X11)))),
% 16.02/16.28      inference('cnf', [status(esa)], [t16_xboole_1])).
% 16.02/16.28  thf('22', plain,
% 16.02/16.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.02/16.28         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 16.02/16.28           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 16.02/16.28      inference('sup+', [status(thm)], ['20', '21'])).
% 16.02/16.28  thf('23', plain,
% 16.02/16.28      (![X0 : $i, X1 : $i]:
% 16.02/16.28         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 16.02/16.28           = (k4_xboole_0 @ X1 @ X0))),
% 16.02/16.28      inference('demod', [status(thm)], ['16', '17'])).
% 16.02/16.28  thf('24', plain,
% 16.02/16.28      (![X16 : $i, X17 : $i, X18 : $i]:
% 16.02/16.28         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 16.02/16.28           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 16.02/16.28      inference('cnf', [status(esa)], [t49_xboole_1])).
% 16.02/16.28  thf('25', plain,
% 16.02/16.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.02/16.28         ((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ X0)))
% 16.02/16.28           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 16.02/16.28      inference('demod', [status(thm)], ['19', '22', '23', '24'])).
% 16.02/16.28  thf('26', plain,
% 16.02/16.28      (((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))
% 16.02/16.28         != (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 16.02/16.28      inference('demod', [status(thm)], ['6', '25'])).
% 16.02/16.28  thf('27', plain, ($false), inference('simplify', [status(thm)], ['26'])).
% 16.02/16.28  
% 16.02/16.28  % SZS output end Refutation
% 16.02/16.28  
% 16.02/16.29  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
