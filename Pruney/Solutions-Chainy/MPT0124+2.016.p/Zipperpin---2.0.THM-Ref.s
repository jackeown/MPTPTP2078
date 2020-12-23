%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8FzfLk52a2

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:54 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   57 (  70 expanded)
%              Number of leaves         :   17 (  29 expanded)
%              Depth                    :   12
%              Number of atoms          :  463 ( 596 expanded)
%              Number of equality atoms :   42 (  54 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t117_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ C @ B )
     => ( ( k4_xboole_0 @ A @ C )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ C @ B )
       => ( ( k4_xboole_0 @ A @ C )
          = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t117_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ sk_A @ sk_C )
 != ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('4',plain,(
    ( k4_xboole_0 @ sk_A @ sk_C )
 != ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','1','2','3'])).

thf('5',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('7',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_B ) @ ( k4_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ ( k4_xboole_0 @ X0 @ sk_C ) )
      = ( k4_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('17',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X2 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C ) ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C ) ) )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ ( k3_xboole_0 @ X0 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('27',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('28',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('31',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_C @ sk_B ) )
      = X0 ) ),
    inference(demod,[status(thm)],['25','26','33'])).

thf('35',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('36',plain,
    ( sk_C
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ( k4_xboole_0 @ sk_A @ sk_C )
 != ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['4','36'])).

thf('38',plain,(
    $false ),
    inference(simplify,[status(thm)],['37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8FzfLk52a2
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:52:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.70  % Solved by: fo/fo7.sh
% 0.46/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.70  % done 313 iterations in 0.255s
% 0.46/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.70  % SZS output start Refutation
% 0.46/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.70  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.70  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.70  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.46/0.70  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.70  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.70  thf(t117_xboole_1, conjecture,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( r1_tarski @ C @ B ) =>
% 0.46/0.70       ( ( k4_xboole_0 @ A @ C ) =
% 0.46/0.70         ( k2_xboole_0 @
% 0.46/0.70           ( k4_xboole_0 @ A @ B ) @ 
% 0.46/0.70           ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) ) ))).
% 0.46/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.70    (~( ![A:$i,B:$i,C:$i]:
% 0.46/0.70        ( ( r1_tarski @ C @ B ) =>
% 0.46/0.70          ( ( k4_xboole_0 @ A @ C ) =
% 0.46/0.70            ( k2_xboole_0 @
% 0.46/0.70              ( k4_xboole_0 @ A @ B ) @ 
% 0.46/0.70              ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) ) ) )),
% 0.46/0.70    inference('cnf.neg', [status(esa)], [t117_xboole_1])).
% 0.46/0.70  thf('0', plain,
% 0.46/0.70      (((k4_xboole_0 @ sk_A @ sk_C)
% 0.46/0.70         != (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 0.46/0.70             (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(t52_xboole_1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.46/0.70       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.46/0.70  thf('1', plain,
% 0.46/0.70      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.46/0.70         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 0.46/0.70           = (k2_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ 
% 0.46/0.70              (k3_xboole_0 @ X16 @ X18)))),
% 0.46/0.70      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.46/0.70  thf(t48_xboole_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.46/0.70  thf('2', plain,
% 0.46/0.70      (![X11 : $i, X12 : $i]:
% 0.46/0.70         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.46/0.70           = (k3_xboole_0 @ X11 @ X12))),
% 0.46/0.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.70  thf(commutativity_k3_xboole_0, axiom,
% 0.46/0.70    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.46/0.70  thf('3', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.70      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.70  thf('4', plain,
% 0.46/0.70      (((k4_xboole_0 @ sk_A @ sk_C)
% 0.46/0.70         != (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_C @ sk_B)))),
% 0.46/0.70      inference('demod', [status(thm)], ['0', '1', '2', '3'])).
% 0.46/0.70  thf('5', plain, ((r1_tarski @ sk_C @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(t12_xboole_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.46/0.70  thf('6', plain,
% 0.46/0.70      (![X2 : $i, X3 : $i]:
% 0.46/0.70         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.46/0.70      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.46/0.70  thf('7', plain, (((k2_xboole_0 @ sk_C @ sk_B) = (sk_B))),
% 0.46/0.70      inference('sup-', [status(thm)], ['5', '6'])).
% 0.46/0.70  thf(t41_xboole_1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.46/0.70       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.46/0.70  thf('8', plain,
% 0.46/0.70      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.70         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 0.46/0.70           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 0.46/0.70      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.46/0.70  thf(t36_xboole_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.46/0.70  thf('9', plain,
% 0.46/0.70      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 0.46/0.70      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.46/0.70  thf('10', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.70         (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 0.46/0.70          (k4_xboole_0 @ X2 @ X1))),
% 0.46/0.70      inference('sup+', [status(thm)], ['8', '9'])).
% 0.46/0.70  thf('11', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (r1_tarski @ (k4_xboole_0 @ X0 @ sk_B) @ (k4_xboole_0 @ X0 @ sk_C))),
% 0.46/0.70      inference('sup+', [status(thm)], ['7', '10'])).
% 0.46/0.70  thf('12', plain,
% 0.46/0.70      (![X2 : $i, X3 : $i]:
% 0.46/0.70         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.46/0.70      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.46/0.70  thf('13', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ (k4_xboole_0 @ X0 @ sk_C))
% 0.46/0.70           = (k4_xboole_0 @ X0 @ sk_C))),
% 0.46/0.70      inference('sup-', [status(thm)], ['11', '12'])).
% 0.46/0.70  thf('14', plain,
% 0.46/0.70      (![X11 : $i, X12 : $i]:
% 0.46/0.70         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.46/0.70           = (k3_xboole_0 @ X11 @ X12))),
% 0.46/0.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.70  thf('15', plain,
% 0.46/0.70      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.70         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 0.46/0.70           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 0.46/0.70      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.46/0.70  thf('16', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.70         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.46/0.70           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 0.46/0.70      inference('sup+', [status(thm)], ['14', '15'])).
% 0.46/0.70  thf(t49_xboole_1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.46/0.70       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.46/0.70  thf('17', plain,
% 0.46/0.70      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.70         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.46/0.70           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 0.46/0.70      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.46/0.70  thf('18', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.70         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X2))
% 0.46/0.70           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 0.46/0.70      inference('demod', [status(thm)], ['16', '17'])).
% 0.46/0.70  thf('19', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_C)))
% 0.46/0.70           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ sk_C)))),
% 0.46/0.70      inference('sup+', [status(thm)], ['13', '18'])).
% 0.46/0.70  thf('20', plain,
% 0.46/0.70      (![X11 : $i, X12 : $i]:
% 0.46/0.70         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.46/0.70           = (k3_xboole_0 @ X11 @ X12))),
% 0.46/0.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.70  thf('21', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_C)))
% 0.46/0.70           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['19', '20'])).
% 0.46/0.70  thf('22', plain,
% 0.46/0.70      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.70         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.46/0.70           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 0.46/0.70      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.46/0.70  thf(t98_xboole_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.46/0.70  thf('23', plain,
% 0.46/0.70      (![X19 : $i, X20 : $i]:
% 0.46/0.70         ((k2_xboole_0 @ X19 @ X20)
% 0.46/0.70           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 0.46/0.70      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.46/0.70  thf('24', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.70         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 0.46/0.70           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.46/0.70      inference('sup+', [status(thm)], ['22', '23'])).
% 0.46/0.70  thf('25', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ (k3_xboole_0 @ X0 @ sk_B))
% 0.46/0.70           = (k5_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ 
% 0.46/0.70              (k3_xboole_0 @ X0 @ sk_C)))),
% 0.46/0.70      inference('sup+', [status(thm)], ['21', '24'])).
% 0.46/0.70  thf('26', plain,
% 0.46/0.70      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.46/0.70         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 0.46/0.70           = (k2_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ 
% 0.46/0.70              (k3_xboole_0 @ X16 @ X18)))),
% 0.46/0.70      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.46/0.70  thf('27', plain,
% 0.46/0.70      (![X11 : $i, X12 : $i]:
% 0.46/0.70         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.46/0.70           = (k3_xboole_0 @ X11 @ X12))),
% 0.46/0.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.70  thf('28', plain,
% 0.46/0.70      (![X19 : $i, X20 : $i]:
% 0.46/0.70         ((k2_xboole_0 @ X19 @ X20)
% 0.46/0.70           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 0.46/0.70      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.46/0.70  thf('29', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 0.46/0.70           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.46/0.70      inference('sup+', [status(thm)], ['27', '28'])).
% 0.46/0.70  thf('30', plain,
% 0.46/0.70      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 0.46/0.70      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.46/0.70  thf('31', plain,
% 0.46/0.70      (![X2 : $i, X3 : $i]:
% 0.46/0.70         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.46/0.70      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.46/0.70  thf('32', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['30', '31'])).
% 0.46/0.70  thf('33', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         ((X1)
% 0.46/0.70           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.46/0.70      inference('demod', [status(thm)], ['29', '32'])).
% 0.46/0.70  thf('34', plain,
% 0.46/0.70      (![X0 : $i]: ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_C @ sk_B)) = (X0))),
% 0.46/0.70      inference('demod', [status(thm)], ['25', '26', '33'])).
% 0.46/0.70  thf('35', plain,
% 0.46/0.70      (![X11 : $i, X12 : $i]:
% 0.46/0.70         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.46/0.70           = (k3_xboole_0 @ X11 @ X12))),
% 0.46/0.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.70  thf('36', plain, (((sk_C) = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['34', '35'])).
% 0.46/0.70  thf('37', plain,
% 0.46/0.70      (((k4_xboole_0 @ sk_A @ sk_C) != (k4_xboole_0 @ sk_A @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['4', '36'])).
% 0.46/0.70  thf('38', plain, ($false), inference('simplify', [status(thm)], ['37'])).
% 0.46/0.70  
% 0.46/0.70  % SZS output end Refutation
% 0.46/0.70  
% 0.57/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
