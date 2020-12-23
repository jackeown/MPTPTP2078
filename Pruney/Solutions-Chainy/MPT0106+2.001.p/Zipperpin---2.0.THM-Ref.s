%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xBRzx0Z8EV

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:10 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :   20 (  21 expanded)
%              Number of leaves         :   10 (  11 expanded)
%              Depth                    :    5
%              Number of atoms          :  182 ( 193 expanded)
%              Number of equality atoms :   13 (  14 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t99_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) @ ( k4_xboole_0 @ B @ ( k2_xboole_0 @ A @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k4_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) @ ( k4_xboole_0 @ B @ ( k2_xboole_0 @ A @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t99_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ sk_C )
 != ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('2',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t42_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X5 @ X7 ) @ X6 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ ( k4_xboole_0 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X3 ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X3 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X3 ) @ ( k4_xboole_0 @ X2 @ X1 ) ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ ( k2_xboole_0 @ X3 @ X0 ) ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('7',plain,(
    ( k4_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ sk_C )
 != ( k4_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','5','6'])).

thf('8',plain,(
    $false ),
    inference(simplify,[status(thm)],['7'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xBRzx0Z8EV
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:31:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.90/1.11  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.90/1.11  % Solved by: fo/fo7.sh
% 0.90/1.11  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.11  % done 84 iterations in 0.647s
% 0.90/1.11  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.90/1.11  % SZS output start Refutation
% 0.90/1.11  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.90/1.11  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.11  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.90/1.11  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.90/1.11  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.11  thf(sk_C_type, type, sk_C: $i).
% 0.90/1.11  thf(t99_xboole_1, conjecture,
% 0.90/1.11    (![A:$i,B:$i,C:$i]:
% 0.90/1.11     ( ( k4_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.90/1.11       ( k2_xboole_0 @
% 0.90/1.11         ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) @ 
% 0.90/1.11         ( k4_xboole_0 @ B @ ( k2_xboole_0 @ A @ C ) ) ) ))).
% 0.90/1.11  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.11    (~( ![A:$i,B:$i,C:$i]:
% 0.90/1.11        ( ( k4_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.90/1.11          ( k2_xboole_0 @
% 0.90/1.11            ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) @ 
% 0.90/1.11            ( k4_xboole_0 @ B @ ( k2_xboole_0 @ A @ C ) ) ) ) )),
% 0.90/1.11    inference('cnf.neg', [status(esa)], [t99_xboole_1])).
% 0.90/1.11  thf('0', plain,
% 0.90/1.11      (((k4_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ sk_C)
% 0.90/1.11         != (k2_xboole_0 @ 
% 0.90/1.11             (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) @ 
% 0.90/1.11             (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C))))),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf(t41_xboole_1, axiom,
% 0.90/1.11    (![A:$i,B:$i,C:$i]:
% 0.90/1.11     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.90/1.11       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.90/1.11  thf('1', plain,
% 0.90/1.11      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.90/1.11         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ X4)
% 0.90/1.11           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X4)))),
% 0.90/1.11      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.90/1.11  thf('2', plain,
% 0.90/1.11      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.90/1.11         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ X4)
% 0.90/1.11           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X4)))),
% 0.90/1.11      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.90/1.11  thf(t42_xboole_1, axiom,
% 0.90/1.11    (![A:$i,B:$i,C:$i]:
% 0.90/1.11     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.90/1.11       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.90/1.11  thf('3', plain,
% 0.90/1.11      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.90/1.11         ((k4_xboole_0 @ (k2_xboole_0 @ X5 @ X7) @ X6)
% 0.90/1.11           = (k2_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ (k4_xboole_0 @ X7 @ X6)))),
% 0.90/1.11      inference('cnf', [status(esa)], [t42_xboole_1])).
% 0.90/1.11  thf('4', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.90/1.11         ((k4_xboole_0 @ (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X3) @ X0)
% 0.90/1.11           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 0.90/1.11              (k4_xboole_0 @ X3 @ X0)))),
% 0.90/1.11      inference('sup+', [status(thm)], ['2', '3'])).
% 0.90/1.11  thf('5', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.90/1.11         ((k4_xboole_0 @ 
% 0.90/1.11           (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X3) @ (k4_xboole_0 @ X2 @ X1)) @ 
% 0.90/1.11           X0)
% 0.90/1.11           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ (k2_xboole_0 @ X3 @ X0)) @ 
% 0.90/1.11              (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 0.90/1.11      inference('sup+', [status(thm)], ['1', '4'])).
% 0.90/1.11  thf(d6_xboole_0, axiom,
% 0.90/1.11    (![A:$i,B:$i]:
% 0.90/1.11     ( ( k5_xboole_0 @ A @ B ) =
% 0.90/1.11       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.90/1.11  thf('6', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((k5_xboole_0 @ X0 @ X1)
% 0.90/1.11           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.90/1.11      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.90/1.11  thf('7', plain,
% 0.90/1.11      (((k4_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ sk_C)
% 0.90/1.11         != (k4_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ sk_C))),
% 0.90/1.11      inference('demod', [status(thm)], ['0', '5', '6'])).
% 0.90/1.11  thf('8', plain, ($false), inference('simplify', [status(thm)], ['7'])).
% 0.90/1.11  
% 0.90/1.11  % SZS output end Refutation
% 0.90/1.11  
% 0.90/1.12  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
