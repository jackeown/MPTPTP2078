%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CwXt6XWzDX

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:57 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   27 (  31 expanded)
%              Number of leaves         :   11 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :  183 ( 225 expanded)
%              Number of equality atoms :   19 (  23 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t30_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ C @ B ) )
        = ( k3_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ B )
       => ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ C @ B ) )
          = ( k3_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t30_xboole_1])).

thf('0',plain,(
    ( k2_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_B ) )
 != ( k3_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('3',plain,(
    ( k2_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
 != ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf('4',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_xboole_0 @ X5 @ X4 )
        = X4 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('6',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('8',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['6','7'])).

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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ ( k3_xboole_0 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) )
      = ( k2_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    ( k2_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
 != ( k2_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['3','12'])).

thf('14',plain,(
    $false ),
    inference(simplify,[status(thm)],['13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CwXt6XWzDX
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:55:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.47/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.66  % Solved by: fo/fo7.sh
% 0.47/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.66  % done 444 iterations in 0.204s
% 0.47/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.66  % SZS output start Refutation
% 0.47/0.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.47/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.66  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.66  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.47/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.66  thf(t30_xboole_1, conjecture,
% 0.47/0.66    (![A:$i,B:$i,C:$i]:
% 0.47/0.66     ( ( r1_tarski @ A @ B ) =>
% 0.47/0.66       ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ C @ B ) ) =
% 0.47/0.66         ( k3_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) ))).
% 0.47/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.66    (~( ![A:$i,B:$i,C:$i]:
% 0.47/0.66        ( ( r1_tarski @ A @ B ) =>
% 0.47/0.66          ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ C @ B ) ) =
% 0.47/0.66            ( k3_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) ) )),
% 0.47/0.66    inference('cnf.neg', [status(esa)], [t30_xboole_1])).
% 0.47/0.66  thf('0', plain,
% 0.47/0.66      (((k2_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_C @ sk_B))
% 0.47/0.66         != (k3_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C) @ sk_B))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(commutativity_k3_xboole_0, axiom,
% 0.47/0.66    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.47/0.66  thf('1', plain,
% 0.47/0.66      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.47/0.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.47/0.66  thf('2', plain,
% 0.47/0.66      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.47/0.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.47/0.66  thf('3', plain,
% 0.47/0.66      (((k2_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 0.47/0.66         != (k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C)))),
% 0.47/0.66      inference('demod', [status(thm)], ['0', '1', '2'])).
% 0.47/0.66  thf('4', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(t12_xboole_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.47/0.66  thf('5', plain,
% 0.47/0.66      (![X4 : $i, X5 : $i]:
% 0.47/0.66         (((k2_xboole_0 @ X5 @ X4) = (X4)) | ~ (r1_tarski @ X5 @ X4))),
% 0.47/0.66      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.47/0.66  thf('6', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.47/0.66      inference('sup-', [status(thm)], ['4', '5'])).
% 0.47/0.66  thf(t21_xboole_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.47/0.66  thf('7', plain,
% 0.47/0.66      (![X6 : $i, X7 : $i]:
% 0.47/0.66         ((k3_xboole_0 @ X6 @ (k2_xboole_0 @ X6 @ X7)) = (X6))),
% 0.47/0.66      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.47/0.66  thf('8', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.47/0.66      inference('sup+', [status(thm)], ['6', '7'])).
% 0.47/0.66  thf('9', plain,
% 0.47/0.66      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.47/0.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.47/0.66  thf(t23_xboole_1, axiom,
% 0.47/0.66    (![A:$i,B:$i,C:$i]:
% 0.47/0.66     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.47/0.66       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.47/0.66  thf('10', plain,
% 0.47/0.66      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.47/0.66         ((k3_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10))
% 0.47/0.66           = (k2_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ (k3_xboole_0 @ X8 @ X10)))),
% 0.47/0.66      inference('cnf', [status(esa)], [t23_xboole_1])).
% 0.47/0.66  thf('11', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.66         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2))
% 0.47/0.66           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X2)))),
% 0.47/0.66      inference('sup+', [status(thm)], ['9', '10'])).
% 0.47/0.66  thf('12', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0))
% 0.47/0.66           = (k2_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)))),
% 0.47/0.66      inference('sup+', [status(thm)], ['8', '11'])).
% 0.47/0.66  thf('13', plain,
% 0.47/0.66      (((k2_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 0.47/0.66         != (k2_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.47/0.66      inference('demod', [status(thm)], ['3', '12'])).
% 0.47/0.66  thf('14', plain, ($false), inference('simplify', [status(thm)], ['13'])).
% 0.47/0.66  
% 0.47/0.66  % SZS output end Refutation
% 0.47/0.66  
% 0.47/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
