%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xOwD3I3nw7

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   39 (  44 expanded)
%              Number of leaves         :   16 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :  183 ( 224 expanded)
%              Number of equality atoms :   24 (  29 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t105_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ( ( k4_xboole_0 @ B @ A )
          = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( r2_xboole_0 @ A @ B )
          & ( ( k4_xboole_0 @ B @ A )
            = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t105_xboole_1])).

thf('0',plain,(
    r2_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('3',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    r2_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( r2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('8',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = sk_A ),
    inference('sup+',[status(thm)],['5','10'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('12',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    sk_B = sk_A ),
    inference(demod,[status(thm)],['11','16'])).

thf('18',plain,(
    r2_xboole_0 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['0','17'])).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( X2 != X3 )
      | ~ ( r2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('20',plain,(
    ! [X3: $i] :
      ~ ( r2_xboole_0 @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    $false ),
    inference('sup-',[status(thm)],['18','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xOwD3I3nw7
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:20:05 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 31 iterations in 0.020s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.21/0.49  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(t105_xboole_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ~( ( r2_xboole_0 @ A @ B ) & 
% 0.21/0.49          ( ( k4_xboole_0 @ B @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i]:
% 0.21/0.49        ( ~( ( r2_xboole_0 @ A @ B ) & 
% 0.21/0.49             ( ( k4_xboole_0 @ B @ A ) = ( k1_xboole_0 ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t105_xboole_1])).
% 0.21/0.49  thf('0', plain, ((r2_xboole_0 @ sk_A @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t48_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X10 : $i, X11 : $i]:
% 0.21/0.49         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.21/0.49           = (k3_xboole_0 @ X10 @ X11))),
% 0.21/0.49      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (((k4_xboole_0 @ sk_B @ k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.21/0.49      inference('sup+', [status(thm)], ['1', '2'])).
% 0.21/0.49  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (((k4_xboole_0 @ sk_B @ k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.49  thf('6', plain, ((r2_xboole_0 @ sk_A @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d8_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.21/0.49       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ~ (r2_xboole_0 @ X2 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.21/0.49  thf('8', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.49  thf(t28_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i]:
% 0.21/0.49         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.21/0.49      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.49  thf('10', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf('11', plain, (((k4_xboole_0 @ sk_B @ k1_xboole_0) = (sk_A))),
% 0.21/0.49      inference('sup+', [status(thm)], ['5', '10'])).
% 0.21/0.49  thf(t2_boole, axiom,
% 0.21/0.49    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X9 : $i]: ((k3_xboole_0 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.49  thf(t100_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X5 : $i, X6 : $i]:
% 0.21/0.49         ((k4_xboole_0 @ X5 @ X6)
% 0.21/0.49           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf(t5_boole, axiom,
% 0.21/0.49    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.49  thf('15', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.21/0.49      inference('cnf', [status(esa)], [t5_boole])).
% 0.21/0.49  thf('16', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.49      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.49  thf('17', plain, (((sk_B) = (sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['11', '16'])).
% 0.21/0.49  thf('18', plain, ((r2_xboole_0 @ sk_A @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['0', '17'])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X2 : $i, X3 : $i]: (((X2) != (X3)) | ~ (r2_xboole_0 @ X2 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.21/0.49  thf('20', plain, (![X3 : $i]: ~ (r2_xboole_0 @ X3 @ X3)),
% 0.21/0.49      inference('simplify', [status(thm)], ['19'])).
% 0.21/0.49  thf('21', plain, ($false), inference('sup-', [status(thm)], ['18', '20'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
