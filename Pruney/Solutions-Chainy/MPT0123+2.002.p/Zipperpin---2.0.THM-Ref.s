%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hrlCPgveBq

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   28 (  32 expanded)
%              Number of leaves         :   10 (  14 expanded)
%              Depth                    :    6
%              Number of atoms          :  213 ( 249 expanded)
%              Number of equality atoms :   20 (  24 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t116_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t116_xboole_1])).

thf('0',plain,(
    ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
 != ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('2',plain,(
    ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
 != ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('7',plain,(
    ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
 != ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['2','5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
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

thf('15',plain,(
    ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
 != ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['7','14'])).

thf('16',plain,(
    $false ),
    inference(simplify,[status(thm)],['15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hrlCPgveBq
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:17:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 17 iterations in 0.046s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(t116_xboole_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 0.20/0.49       ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.49        ( ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 0.20/0.49          ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t116_xboole_1])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 0.20/0.49         != (k3_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 0.20/0.49             (k3_xboole_0 @ sk_A @ sk_C)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t16_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.49       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.49         ((k3_xboole_0 @ (k3_xboole_0 @ X2 @ X3) @ X4)
% 0.20/0.49           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 0.20/0.49         != (k3_xboole_0 @ sk_A @ 
% 0.20/0.49             (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_C))))),
% 0.20/0.49      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.49         ((k3_xboole_0 @ (k3_xboole_0 @ X2 @ X3) @ X4)
% 0.20/0.49           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.20/0.49  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 0.20/0.49           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['3', '4'])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 0.20/0.49         != (k3_xboole_0 @ sk_A @ 
% 0.20/0.49             (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 0.20/0.49      inference('demod', [status(thm)], ['2', '5', '6'])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.49  thf(t17_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 0.20/0.49      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.20/0.49  thf(t28_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X7 : $i, X8 : $i]:
% 0.20/0.49         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.20/0.49      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 0.20/0.49           = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.49         ((k3_xboole_0 @ (k3_xboole_0 @ X2 @ X3) @ X4)
% 0.20/0.49           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.20/0.49           = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.49      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.20/0.49           = (k3_xboole_0 @ X1 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['8', '13'])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 0.20/0.49         != (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['7', '14'])).
% 0.20/0.49  thf('16', plain, ($false), inference('simplify', [status(thm)], ['15'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
