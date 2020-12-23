%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nxBpwr2yG3

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:54 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   35 (  45 expanded)
%              Number of leaves         :   13 (  19 expanded)
%              Depth                    :    9
%              Number of atoms          :  206 ( 299 expanded)
%              Number of equality atoms :    8 (  11 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t27_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D ) )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ ( k3_xboole_0 @ B @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ C @ D ) )
       => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ ( k3_xboole_0 @ B @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X2 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_C @ X0 ) @ sk_D ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X2 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X9 @ X11 )
      | ( r1_tarski @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ X1 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['7','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('19',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    $false ),
    inference(demod,[status(thm)],['0','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nxBpwr2yG3
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:08:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.38/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.57  % Solved by: fo/fo7.sh
% 0.38/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.57  % done 240 iterations in 0.118s
% 0.38/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.57  % SZS output start Refutation
% 0.38/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.57  thf(sk_D_type, type, sk_D: $i).
% 0.38/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.57  thf(t27_xboole_1, conjecture,
% 0.38/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.57     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.38/0.57       ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ ( k3_xboole_0 @ B @ D ) ) ))).
% 0.38/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.57    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.57        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.38/0.57          ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ ( k3_xboole_0 @ B @ D ) ) ) )),
% 0.38/0.57    inference('cnf.neg', [status(esa)], [t27_xboole_1])).
% 0.38/0.57  thf('0', plain,
% 0.38/0.57      (~ (r1_tarski @ (k3_xboole_0 @ sk_A @ sk_C) @ (k3_xboole_0 @ sk_B @ sk_D))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('1', plain, ((r1_tarski @ sk_C @ sk_D)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(t17_xboole_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.38/0.57  thf('2', plain,
% 0.38/0.57      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 0.38/0.57      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.38/0.57  thf(t12_xboole_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.38/0.57  thf('3', plain,
% 0.38/0.57      (![X5 : $i, X6 : $i]:
% 0.38/0.57         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 0.38/0.57      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.38/0.57  thf('4', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.57  thf(t11_xboole_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.38/0.57  thf('5', plain,
% 0.38/0.57      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.38/0.57         ((r1_tarski @ X2 @ X3) | ~ (r1_tarski @ (k2_xboole_0 @ X2 @ X4) @ X3))),
% 0.38/0.57      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.38/0.57  thf('6', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.57         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k3_xboole_0 @ X0 @ X2) @ X1))),
% 0.38/0.57      inference('sup-', [status(thm)], ['4', '5'])).
% 0.38/0.57  thf('7', plain, (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ sk_C @ X0) @ sk_D)),
% 0.38/0.57      inference('sup-', [status(thm)], ['1', '6'])).
% 0.38/0.57  thf('8', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(commutativity_k3_xboole_0, axiom,
% 0.38/0.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.38/0.57  thf('9', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.57  thf('10', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.57  thf('11', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 0.38/0.57      inference('sup+', [status(thm)], ['9', '10'])).
% 0.38/0.57  thf('12', plain,
% 0.38/0.57      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.38/0.57         ((r1_tarski @ X2 @ X3) | ~ (r1_tarski @ (k2_xboole_0 @ X2 @ X4) @ X3))),
% 0.38/0.57      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.38/0.57  thf('13', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.57         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k3_xboole_0 @ X2 @ X0) @ X1))),
% 0.38/0.57      inference('sup-', [status(thm)], ['11', '12'])).
% 0.38/0.57  thf('14', plain,
% 0.38/0.57      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ sk_B)),
% 0.38/0.57      inference('sup-', [status(thm)], ['8', '13'])).
% 0.38/0.57  thf(t19_xboole_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.38/0.57       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.38/0.57  thf('15', plain,
% 0.38/0.57      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.38/0.57         (~ (r1_tarski @ X9 @ X10)
% 0.38/0.57          | ~ (r1_tarski @ X9 @ X11)
% 0.38/0.57          | (r1_tarski @ X9 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.38/0.57      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.38/0.57  thf('16', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         ((r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ (k3_xboole_0 @ sk_B @ X1))
% 0.38/0.57          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ X1))),
% 0.38/0.57      inference('sup-', [status(thm)], ['14', '15'])).
% 0.38/0.57  thf('17', plain,
% 0.38/0.57      ((r1_tarski @ (k3_xboole_0 @ sk_C @ sk_A) @ (k3_xboole_0 @ sk_B @ sk_D))),
% 0.38/0.57      inference('sup-', [status(thm)], ['7', '16'])).
% 0.38/0.57  thf('18', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.57  thf('19', plain,
% 0.38/0.57      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_C) @ (k3_xboole_0 @ sk_B @ sk_D))),
% 0.38/0.57      inference('demod', [status(thm)], ['17', '18'])).
% 0.38/0.57  thf('20', plain, ($false), inference('demod', [status(thm)], ['0', '19'])).
% 0.38/0.57  
% 0.38/0.57  % SZS output end Refutation
% 0.38/0.57  
% 0.38/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
