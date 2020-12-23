%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EBZZDhQCCj

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:17 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   52 (  86 expanded)
%              Number of leaves         :   16 (  34 expanded)
%              Depth                    :   12
%              Number of atoms          :  322 ( 582 expanded)
%              Number of equality atoms :   30 (  60 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t76_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_xboole_0 @ A @ B )
       => ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_C @ sk_B ) ) ),
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
    ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf('4',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('6',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('8',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['10'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ ( k3_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('16',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('21',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['14','21','22'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('24',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ( r1_xboole_0 @ X14 @ X17 )
      | ~ ( r1_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','25'])).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k3_xboole_0 @ sk_B @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['3','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EBZZDhQCCj
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:30:33 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.54/0.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.54/0.71  % Solved by: fo/fo7.sh
% 0.54/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.71  % done 896 iterations in 0.265s
% 0.54/0.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.54/0.71  % SZS output start Refutation
% 0.54/0.71  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.54/0.71  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.54/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.54/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.54/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.71  thf(sk_C_type, type, sk_C: $i).
% 0.54/0.71  thf(t76_xboole_1, conjecture,
% 0.54/0.71    (![A:$i,B:$i,C:$i]:
% 0.54/0.71     ( ( r1_xboole_0 @ A @ B ) =>
% 0.54/0.71       ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ))).
% 0.54/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.71    (~( ![A:$i,B:$i,C:$i]:
% 0.54/0.71        ( ( r1_xboole_0 @ A @ B ) =>
% 0.54/0.71          ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ) )),
% 0.54/0.71    inference('cnf.neg', [status(esa)], [t76_xboole_1])).
% 0.54/0.71  thf('0', plain,
% 0.54/0.71      (~ (r1_xboole_0 @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 0.54/0.71          (k3_xboole_0 @ sk_C @ sk_B))),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf(commutativity_k3_xboole_0, axiom,
% 0.54/0.71    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.54/0.71  thf('1', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.54/0.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.54/0.71  thf('2', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.54/0.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.54/0.71  thf('3', plain,
% 0.54/0.71      (~ (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_C) @ 
% 0.54/0.71          (k3_xboole_0 @ sk_B @ sk_C))),
% 0.54/0.71      inference('demod', [status(thm)], ['0', '1', '2'])).
% 0.54/0.71  thf('4', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf(d7_xboole_0, axiom,
% 0.54/0.71    (![A:$i,B:$i]:
% 0.54/0.71     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.54/0.71       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.54/0.71  thf('5', plain,
% 0.54/0.71      (![X2 : $i, X3 : $i]:
% 0.54/0.71         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.54/0.71      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.54/0.71  thf('6', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.54/0.71      inference('sup-', [status(thm)], ['4', '5'])).
% 0.54/0.71  thf('7', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.54/0.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.54/0.71  thf('8', plain,
% 0.54/0.71      (![X2 : $i, X4 : $i]:
% 0.54/0.71         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.54/0.71      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.54/0.71  thf('9', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 0.54/0.71      inference('sup-', [status(thm)], ['7', '8'])).
% 0.54/0.71  thf('10', plain,
% 0.54/0.71      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_A))),
% 0.54/0.71      inference('sup-', [status(thm)], ['6', '9'])).
% 0.54/0.71  thf('11', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 0.54/0.71      inference('simplify', [status(thm)], ['10'])).
% 0.54/0.71  thf(t3_boole, axiom,
% 0.54/0.71    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.54/0.71  thf('12', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.54/0.71      inference('cnf', [status(esa)], [t3_boole])).
% 0.54/0.71  thf(t52_xboole_1, axiom,
% 0.54/0.71    (![A:$i,B:$i,C:$i]:
% 0.54/0.71     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.54/0.71       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.54/0.71  thf('13', plain,
% 0.54/0.71      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.54/0.71         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X13))
% 0.54/0.71           = (k2_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ 
% 0.54/0.71              (k3_xboole_0 @ X11 @ X13)))),
% 0.54/0.71      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.54/0.71  thf('14', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X1))
% 0.54/0.71           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.54/0.71      inference('sup+', [status(thm)], ['12', '13'])).
% 0.54/0.71  thf('15', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.54/0.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.54/0.71  thf(t2_boole, axiom,
% 0.54/0.71    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.54/0.71  thf('16', plain,
% 0.54/0.71      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.71      inference('cnf', [status(esa)], [t2_boole])).
% 0.54/0.71  thf('17', plain,
% 0.54/0.71      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.54/0.71      inference('sup+', [status(thm)], ['15', '16'])).
% 0.54/0.71  thf(t47_xboole_1, axiom,
% 0.54/0.71    (![A:$i,B:$i]:
% 0.54/0.71     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.54/0.71  thf('18', plain,
% 0.54/0.71      (![X7 : $i, X8 : $i]:
% 0.54/0.71         ((k4_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8))
% 0.54/0.71           = (k4_xboole_0 @ X7 @ X8))),
% 0.54/0.71      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.54/0.71  thf('19', plain,
% 0.54/0.71      (![X0 : $i]:
% 0.54/0.71         ((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.54/0.71           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.54/0.71      inference('sup+', [status(thm)], ['17', '18'])).
% 0.54/0.71  thf('20', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.54/0.71      inference('cnf', [status(esa)], [t3_boole])).
% 0.54/0.71  thf('21', plain,
% 0.54/0.71      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.54/0.71      inference('demod', [status(thm)], ['19', '20'])).
% 0.54/0.71  thf('22', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.54/0.71      inference('cnf', [status(esa)], [t3_boole])).
% 0.54/0.71  thf('23', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((X0) = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.54/0.71      inference('demod', [status(thm)], ['14', '21', '22'])).
% 0.54/0.71  thf(t70_xboole_1, axiom,
% 0.54/0.71    (![A:$i,B:$i,C:$i]:
% 0.54/0.71     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.54/0.71            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.54/0.71       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.54/0.71            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.54/0.71  thf('24', plain,
% 0.54/0.71      (![X14 : $i, X15 : $i, X17 : $i]:
% 0.54/0.71         ((r1_xboole_0 @ X14 @ X17)
% 0.54/0.71          | ~ (r1_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X17)))),
% 0.54/0.71      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.54/0.71  thf('25', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.71         (~ (r1_xboole_0 @ X2 @ X0)
% 0.54/0.71          | (r1_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.54/0.71      inference('sup-', [status(thm)], ['23', '24'])).
% 0.54/0.71  thf('26', plain,
% 0.54/0.71      (![X0 : $i]: (r1_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0))),
% 0.54/0.71      inference('sup-', [status(thm)], ['11', '25'])).
% 0.54/0.71  thf('27', plain,
% 0.54/0.71      (![X2 : $i, X3 : $i]:
% 0.54/0.71         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.54/0.71      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.54/0.71  thf('28', plain,
% 0.54/0.71      (![X0 : $i]:
% 0.54/0.71         ((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0)) = (k1_xboole_0))),
% 0.54/0.71      inference('sup-', [status(thm)], ['26', '27'])).
% 0.54/0.71  thf('29', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 0.54/0.71      inference('sup-', [status(thm)], ['7', '8'])).
% 0.54/0.71  thf('30', plain,
% 0.54/0.71      (![X0 : $i]:
% 0.54/0.71         (((k1_xboole_0) != (k1_xboole_0))
% 0.54/0.71          | (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B))),
% 0.54/0.71      inference('sup-', [status(thm)], ['28', '29'])).
% 0.54/0.71  thf('31', plain,
% 0.54/0.71      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B)),
% 0.54/0.71      inference('simplify', [status(thm)], ['30'])).
% 0.54/0.71  thf('32', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.71         (~ (r1_xboole_0 @ X2 @ X0)
% 0.54/0.71          | (r1_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.54/0.71      inference('sup-', [status(thm)], ['23', '24'])).
% 0.54/0.71  thf('33', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ (k3_xboole_0 @ sk_B @ X1))),
% 0.54/0.71      inference('sup-', [status(thm)], ['31', '32'])).
% 0.54/0.71  thf('34', plain, ($false), inference('demod', [status(thm)], ['3', '33'])).
% 0.54/0.71  
% 0.54/0.71  % SZS output end Refutation
% 0.54/0.71  
% 0.54/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
