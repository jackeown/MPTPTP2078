%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UNTBwIPKOw

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:47 EST 2020

% Result     : Theorem 3.40s
% Output     : Refutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :   39 (  50 expanded)
%              Number of leaves         :   11 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :  243 ( 352 expanded)
%              Number of equality atoms :   16 (  22 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t13_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ C @ D ) )
       => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t13_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_C ) @ ( k2_xboole_0 @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('3',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_D )
    = sk_D ),
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

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k2_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_C @ ( k2_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['3','10'])).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_C @ ( k2_xboole_0 @ X0 @ sk_D ) )
      = ( k2_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('16',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k2_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B @ X0 )
      = ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k2_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('20',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X2 @ X1 ) @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X1 @ sk_A ) @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_C @ sk_A ) @ ( k2_xboole_0 @ sk_B @ sk_D ) ),
    inference('sup+',[status(thm)],['13','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('25',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_C ) @ ( k2_xboole_0 @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    $false ),
    inference(demod,[status(thm)],['0','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UNTBwIPKOw
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:47:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 3.40/3.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.40/3.57  % Solved by: fo/fo7.sh
% 3.40/3.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.40/3.57  % done 1427 iterations in 3.118s
% 3.40/3.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.40/3.57  % SZS output start Refutation
% 3.40/3.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.40/3.57  thf(sk_A_type, type, sk_A: $i).
% 3.40/3.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.40/3.57  thf(sk_C_type, type, sk_C: $i).
% 3.40/3.57  thf(sk_D_type, type, sk_D: $i).
% 3.40/3.57  thf(sk_B_type, type, sk_B: $i).
% 3.40/3.57  thf(t13_xboole_1, conjecture,
% 3.40/3.57    (![A:$i,B:$i,C:$i,D:$i]:
% 3.40/3.57     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 3.40/3.57       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ D ) ) ))).
% 3.40/3.57  thf(zf_stmt_0, negated_conjecture,
% 3.40/3.57    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 3.40/3.57        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 3.40/3.57          ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ D ) ) ) )),
% 3.40/3.57    inference('cnf.neg', [status(esa)], [t13_xboole_1])).
% 3.40/3.57  thf('0', plain,
% 3.40/3.57      (~ (r1_tarski @ (k2_xboole_0 @ sk_A @ sk_C) @ (k2_xboole_0 @ sk_B @ sk_D))),
% 3.40/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.57  thf('1', plain, ((r1_tarski @ sk_C @ sk_D)),
% 3.40/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.57  thf(t12_xboole_1, axiom,
% 3.40/3.57    (![A:$i,B:$i]:
% 3.40/3.57     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 3.40/3.57  thf('2', plain,
% 3.40/3.57      (![X2 : $i, X3 : $i]:
% 3.40/3.57         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 3.40/3.57      inference('cnf', [status(esa)], [t12_xboole_1])).
% 3.40/3.57  thf('3', plain, (((k2_xboole_0 @ sk_C @ sk_D) = (sk_D))),
% 3.40/3.57      inference('sup-', [status(thm)], ['1', '2'])).
% 3.40/3.57  thf(commutativity_k2_xboole_0, axiom,
% 3.40/3.57    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 3.40/3.57  thf('4', plain,
% 3.40/3.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.40/3.57      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.40/3.57  thf(t4_xboole_1, axiom,
% 3.40/3.57    (![A:$i,B:$i,C:$i]:
% 3.40/3.57     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 3.40/3.57       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 3.40/3.57  thf('5', plain,
% 3.40/3.57      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.40/3.57         ((k2_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ X6)
% 3.40/3.57           = (k2_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 3.40/3.57      inference('cnf', [status(esa)], [t4_xboole_1])).
% 3.40/3.57  thf('6', plain,
% 3.40/3.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.40/3.57      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.40/3.57  thf(t7_xboole_1, axiom,
% 3.40/3.57    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 3.40/3.57  thf('7', plain,
% 3.40/3.57      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 3.40/3.57      inference('cnf', [status(esa)], [t7_xboole_1])).
% 3.40/3.57  thf('8', plain,
% 3.40/3.57      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 3.40/3.57      inference('sup+', [status(thm)], ['6', '7'])).
% 3.40/3.57  thf('9', plain,
% 3.40/3.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.40/3.57         (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 3.40/3.57      inference('sup+', [status(thm)], ['5', '8'])).
% 3.40/3.57  thf('10', plain,
% 3.40/3.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.40/3.57         (r1_tarski @ X1 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 3.40/3.57      inference('sup+', [status(thm)], ['4', '9'])).
% 3.40/3.57  thf('11', plain,
% 3.40/3.57      (![X0 : $i]: (r1_tarski @ sk_C @ (k2_xboole_0 @ X0 @ sk_D))),
% 3.40/3.57      inference('sup+', [status(thm)], ['3', '10'])).
% 3.40/3.57  thf('12', plain,
% 3.40/3.57      (![X2 : $i, X3 : $i]:
% 3.40/3.57         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 3.40/3.57      inference('cnf', [status(esa)], [t12_xboole_1])).
% 3.40/3.57  thf('13', plain,
% 3.40/3.57      (![X0 : $i]:
% 3.40/3.57         ((k2_xboole_0 @ sk_C @ (k2_xboole_0 @ X0 @ sk_D))
% 3.40/3.57           = (k2_xboole_0 @ X0 @ sk_D))),
% 3.40/3.57      inference('sup-', [status(thm)], ['11', '12'])).
% 3.40/3.57  thf('14', plain, ((r1_tarski @ sk_A @ sk_B)),
% 3.40/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.57  thf('15', plain,
% 3.40/3.57      (![X2 : $i, X3 : $i]:
% 3.40/3.57         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 3.40/3.57      inference('cnf', [status(esa)], [t12_xboole_1])).
% 3.40/3.57  thf('16', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 3.40/3.57      inference('sup-', [status(thm)], ['14', '15'])).
% 3.40/3.57  thf('17', plain,
% 3.40/3.57      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.40/3.57         ((k2_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ X6)
% 3.40/3.57           = (k2_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 3.40/3.57      inference('cnf', [status(esa)], [t4_xboole_1])).
% 3.40/3.57  thf('18', plain,
% 3.40/3.57      (![X0 : $i]:
% 3.40/3.57         ((k2_xboole_0 @ sk_B @ X0)
% 3.40/3.57           = (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))),
% 3.40/3.57      inference('sup+', [status(thm)], ['16', '17'])).
% 3.40/3.57  thf('19', plain,
% 3.40/3.57      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.40/3.57         ((k2_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ X6)
% 3.40/3.57           = (k2_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 3.40/3.57      inference('cnf', [status(esa)], [t4_xboole_1])).
% 3.40/3.57  thf('20', plain,
% 3.40/3.57      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 3.40/3.57      inference('cnf', [status(esa)], [t7_xboole_1])).
% 3.40/3.57  thf('21', plain,
% 3.40/3.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.40/3.57         (r1_tarski @ (k2_xboole_0 @ X2 @ X1) @ 
% 3.40/3.57          (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 3.40/3.57      inference('sup+', [status(thm)], ['19', '20'])).
% 3.40/3.57  thf('22', plain,
% 3.40/3.57      (![X0 : $i, X1 : $i]:
% 3.40/3.57         (r1_tarski @ (k2_xboole_0 @ X1 @ sk_A) @ 
% 3.40/3.57          (k2_xboole_0 @ X1 @ (k2_xboole_0 @ sk_B @ X0)))),
% 3.40/3.57      inference('sup+', [status(thm)], ['18', '21'])).
% 3.40/3.57  thf('23', plain,
% 3.40/3.57      ((r1_tarski @ (k2_xboole_0 @ sk_C @ sk_A) @ (k2_xboole_0 @ sk_B @ sk_D))),
% 3.40/3.57      inference('sup+', [status(thm)], ['13', '22'])).
% 3.40/3.57  thf('24', plain,
% 3.40/3.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.40/3.57      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.40/3.57  thf('25', plain,
% 3.40/3.57      ((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_C) @ (k2_xboole_0 @ sk_B @ sk_D))),
% 3.40/3.57      inference('demod', [status(thm)], ['23', '24'])).
% 3.40/3.57  thf('26', plain, ($false), inference('demod', [status(thm)], ['0', '25'])).
% 3.40/3.57  
% 3.40/3.57  % SZS output end Refutation
% 3.40/3.57  
% 3.40/3.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
