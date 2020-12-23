%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yEmCGosHMB

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:47 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :   34 (  41 expanded)
%              Number of leaves         :   12 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :  197 ( 270 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
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

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X2 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_C @ ( k2_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf('10',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('12',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('14',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X2 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('17',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X11 @ X10 )
      | ( r1_tarski @ ( k2_xboole_0 @ X9 @ X11 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_A @ X1 ) @ ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_C ) @ ( k2_xboole_0 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['9','18'])).

thf('20',plain,(
    $false ),
    inference(demod,[status(thm)],['0','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yEmCGosHMB
% 0.14/0.36  % Computer   : n002.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 17:39:22 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.68/0.87  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.68/0.87  % Solved by: fo/fo7.sh
% 0.68/0.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.87  % done 742 iterations in 0.398s
% 0.68/0.87  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.68/0.87  % SZS output start Refutation
% 0.68/0.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.68/0.87  thf(sk_B_type, type, sk_B: $i).
% 0.68/0.87  thf(sk_D_type, type, sk_D: $i).
% 0.68/0.87  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.87  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.68/0.87  thf(sk_C_type, type, sk_C: $i).
% 0.68/0.87  thf(t13_xboole_1, conjecture,
% 0.68/0.87    (![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.87     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.68/0.87       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ D ) ) ))).
% 0.68/0.87  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.87    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.87        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.68/0.87          ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ D ) ) ) )),
% 0.68/0.87    inference('cnf.neg', [status(esa)], [t13_xboole_1])).
% 0.68/0.87  thf('0', plain,
% 0.68/0.87      (~ (r1_tarski @ (k2_xboole_0 @ sk_A @ sk_C) @ (k2_xboole_0 @ sk_B @ sk_D))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('1', plain, ((r1_tarski @ sk_C @ sk_D)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf(t12_xboole_1, axiom,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.68/0.87  thf('2', plain,
% 0.68/0.87      (![X5 : $i, X6 : $i]:
% 0.68/0.87         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 0.68/0.87      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.68/0.87  thf('3', plain, (((k2_xboole_0 @ sk_C @ sk_D) = (sk_D))),
% 0.68/0.87      inference('sup-', [status(thm)], ['1', '2'])).
% 0.68/0.87  thf(commutativity_k2_xboole_0, axiom,
% 0.68/0.87    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.68/0.87  thf('4', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.68/0.87      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.68/0.87  thf(t7_xboole_1, axiom,
% 0.68/0.87    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.68/0.87  thf('5', plain,
% 0.68/0.87      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 0.68/0.87      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.68/0.87  thf('6', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.68/0.87      inference('sup+', [status(thm)], ['4', '5'])).
% 0.68/0.87  thf(t11_xboole_1, axiom,
% 0.68/0.87    (![A:$i,B:$i,C:$i]:
% 0.68/0.87     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.68/0.87  thf('7', plain,
% 0.68/0.87      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.68/0.87         ((r1_tarski @ X2 @ X3) | ~ (r1_tarski @ (k2_xboole_0 @ X2 @ X4) @ X3))),
% 0.68/0.87      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.68/0.87  thf('8', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.87         (r1_tarski @ X1 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['6', '7'])).
% 0.68/0.87  thf('9', plain, (![X0 : $i]: (r1_tarski @ sk_C @ (k2_xboole_0 @ X0 @ sk_D))),
% 0.68/0.87      inference('sup+', [status(thm)], ['3', '8'])).
% 0.68/0.87  thf('10', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('11', plain,
% 0.68/0.87      (![X5 : $i, X6 : $i]:
% 0.68/0.87         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 0.68/0.87      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.68/0.87  thf('12', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.68/0.87      inference('sup-', [status(thm)], ['10', '11'])).
% 0.68/0.87  thf('13', plain,
% 0.68/0.87      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 0.68/0.87      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.68/0.87  thf('14', plain,
% 0.68/0.87      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.68/0.87         ((r1_tarski @ X2 @ X3) | ~ (r1_tarski @ (k2_xboole_0 @ X2 @ X4) @ X3))),
% 0.68/0.87      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.68/0.87  thf('15', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.87         (r1_tarski @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 0.68/0.87      inference('sup-', [status(thm)], ['13', '14'])).
% 0.68/0.87  thf('16', plain,
% 0.68/0.87      (![X0 : $i]: (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ X0))),
% 0.68/0.87      inference('sup+', [status(thm)], ['12', '15'])).
% 0.68/0.87  thf(t8_xboole_1, axiom,
% 0.68/0.87    (![A:$i,B:$i,C:$i]:
% 0.68/0.87     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.68/0.87       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.68/0.87  thf('17', plain,
% 0.68/0.87      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.68/0.87         (~ (r1_tarski @ X9 @ X10)
% 0.68/0.87          | ~ (r1_tarski @ X11 @ X10)
% 0.68/0.87          | (r1_tarski @ (k2_xboole_0 @ X9 @ X11) @ X10))),
% 0.68/0.87      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.68/0.87  thf('18', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]:
% 0.68/0.87         ((r1_tarski @ (k2_xboole_0 @ sk_A @ X1) @ (k2_xboole_0 @ sk_B @ X0))
% 0.68/0.87          | ~ (r1_tarski @ X1 @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['16', '17'])).
% 0.68/0.87  thf('19', plain,
% 0.68/0.87      ((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_C) @ (k2_xboole_0 @ sk_B @ sk_D))),
% 0.68/0.87      inference('sup-', [status(thm)], ['9', '18'])).
% 0.68/0.87  thf('20', plain, ($false), inference('demod', [status(thm)], ['0', '19'])).
% 0.68/0.87  
% 0.68/0.87  % SZS output end Refutation
% 0.68/0.87  
% 0.68/0.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
