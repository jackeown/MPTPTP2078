%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BwPhs72oNG

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   32 (  41 expanded)
%              Number of leaves         :   12 (  17 expanded)
%              Depth                    :    8
%              Number of atoms          :  167 ( 231 expanded)
%              Number of equality atoms :   11 (  14 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t109_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t109_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('5',plain,(
    r1_tarski @ sk_A @ sk_A ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('7',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('11',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B ) ),
    inference('sup+',[status(thm)],['9','16'])).

thf('18',plain,(
    $false ),
    inference(demod,[status(thm)],['0','17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BwPhs72oNG
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:18:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 102 iterations in 0.061s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(t109_xboole_1, conjecture,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.52        ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t109_xboole_1])).
% 0.20/0.52  thf('0', plain, (~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t28_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i]:
% 0.20/0.52         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.20/0.52      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.52  thf('3', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.52  thf(t17_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 0.20/0.52      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.20/0.52  thf('5', plain, ((r1_tarski @ sk_A @ sk_A)),
% 0.20/0.52      inference('sup+', [status(thm)], ['3', '4'])).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i]:
% 0.20/0.52         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.20/0.52      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.52  thf('7', plain, (((k3_xboole_0 @ sk_A @ sk_A) = (sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.52  thf(t49_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.20/0.52       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.52         ((k3_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X16))
% 0.20/0.52           = (k4_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ X16))),
% 0.20/0.52      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ X0))
% 0.20/0.52           = (k4_xboole_0 @ sk_A @ X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['7', '8'])).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 0.20/0.52      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.20/0.52  thf('11', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.52  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.52  thf(t18_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.52         ((r1_tarski @ X9 @ X10)
% 0.20/0.52          | ~ (r1_tarski @ X9 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t18_xboole_1])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (![X0 : $i]: (~ (r1_tarski @ X0 @ sk_A) | (r1_tarski @ X0 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['11', '14'])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ sk_B)),
% 0.20/0.52      inference('sup-', [status(thm)], ['10', '15'])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_A @ X0) @ sk_B)),
% 0.20/0.52      inference('sup+', [status(thm)], ['9', '16'])).
% 0.20/0.52  thf('18', plain, ($false), inference('demod', [status(thm)], ['0', '17'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
