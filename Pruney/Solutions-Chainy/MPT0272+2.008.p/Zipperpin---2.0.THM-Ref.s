%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ebnp0sIkwv

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:26 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   47 (  53 expanded)
%              Number of leaves         :   18 (  23 expanded)
%              Depth                    :   12
%              Number of atoms          :  304 ( 361 expanded)
%              Number of equality atoms :   42 (  50 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('0',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('1',plain,(
    ! [X56: $i,X57: $i] :
      ( ( X57
        = ( k1_tarski @ X56 ) )
      | ( X57 = k1_xboole_0 )
      | ~ ( r1_tarski @ X57 @ ( k1_tarski @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ X25 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t69_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
        | ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t69_zfmisc_1])).

thf('12',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('16',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('22',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('23',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','24'])).

thf('26',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ebnp0sIkwv
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:39:25 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.35/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.55  % Solved by: fo/fo7.sh
% 0.35/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.55  % done 274 iterations in 0.093s
% 0.35/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.55  % SZS output start Refutation
% 0.35/0.55  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.35/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.35/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.35/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.35/0.55  thf(t17_xboole_1, axiom,
% 0.35/0.55    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.35/0.55  thf('0', plain,
% 0.35/0.55      (![X11 : $i, X12 : $i]: (r1_tarski @ (k3_xboole_0 @ X11 @ X12) @ X11)),
% 0.35/0.55      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.35/0.55  thf(l3_zfmisc_1, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.35/0.55       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.35/0.55  thf('1', plain,
% 0.35/0.55      (![X56 : $i, X57 : $i]:
% 0.35/0.55         (((X57) = (k1_tarski @ X56))
% 0.35/0.55          | ((X57) = (k1_xboole_0))
% 0.35/0.55          | ~ (r1_tarski @ X57 @ (k1_tarski @ X56)))),
% 0.35/0.55      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.35/0.55  thf('2', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]:
% 0.35/0.55         (((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 0.35/0.55          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.35/0.55  thf(t100_xboole_1, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.35/0.55  thf('3', plain,
% 0.35/0.55      (![X9 : $i, X10 : $i]:
% 0.35/0.55         ((k4_xboole_0 @ X9 @ X10)
% 0.35/0.55           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.35/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.35/0.55  thf('4', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]:
% 0.35/0.55         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.35/0.55            = (k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))
% 0.35/0.55          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 0.35/0.55      inference('sup+', [status(thm)], ['2', '3'])).
% 0.35/0.55  thf(t92_xboole_1, axiom,
% 0.35/0.55    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.35/0.55  thf('5', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ X25) = (k1_xboole_0))),
% 0.35/0.55      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.35/0.55  thf('6', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]:
% 0.35/0.55         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 0.35/0.55          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 0.35/0.55      inference('demod', [status(thm)], ['4', '5'])).
% 0.35/0.55  thf(commutativity_k3_xboole_0, axiom,
% 0.35/0.55    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.35/0.55  thf('7', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.35/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.35/0.55  thf(d7_xboole_0, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.35/0.55       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.35/0.55  thf('8', plain,
% 0.35/0.55      (![X4 : $i, X6 : $i]:
% 0.35/0.55         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 0.35/0.55      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.35/0.55  thf('9', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]:
% 0.35/0.55         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 0.35/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.35/0.55  thf('10', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]:
% 0.35/0.55         (((k1_xboole_0) != (k1_xboole_0))
% 0.35/0.55          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0))
% 0.35/0.55          | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['6', '9'])).
% 0.35/0.55  thf('11', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]:
% 0.35/0.55         ((r1_xboole_0 @ X0 @ (k1_tarski @ X1))
% 0.35/0.55          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 0.35/0.55      inference('simplify', [status(thm)], ['10'])).
% 0.35/0.55  thf(t69_zfmisc_1, conjecture,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.35/0.55       ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) ))).
% 0.35/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.55    (~( ![A:$i,B:$i]:
% 0.35/0.55        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.35/0.55          ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) ) )),
% 0.35/0.55    inference('cnf.neg', [status(esa)], [t69_zfmisc_1])).
% 0.35/0.55  thf('12', plain,
% 0.35/0.55      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('13', plain,
% 0.35/0.55      ((((k1_xboole_0) != (k1_xboole_0))
% 0.35/0.55        | (r1_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.35/0.55  thf('14', plain, ((r1_xboole_0 @ sk_B @ (k1_tarski @ sk_A))),
% 0.35/0.55      inference('simplify', [status(thm)], ['13'])).
% 0.35/0.55  thf('15', plain,
% 0.35/0.55      (![X4 : $i, X5 : $i]:
% 0.35/0.55         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.35/0.55      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.35/0.55  thf('16', plain,
% 0.35/0.55      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.35/0.55      inference('sup-', [status(thm)], ['14', '15'])).
% 0.35/0.55  thf('17', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.35/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.35/0.55  thf('18', plain,
% 0.35/0.55      (![X9 : $i, X10 : $i]:
% 0.35/0.55         ((k4_xboole_0 @ X9 @ X10)
% 0.35/0.55           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.35/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.35/0.55  thf('19', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]:
% 0.35/0.55         ((k4_xboole_0 @ X0 @ X1)
% 0.35/0.55           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.35/0.55      inference('sup+', [status(thm)], ['17', '18'])).
% 0.35/0.55  thf('20', plain,
% 0.35/0.55      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.35/0.55         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0))),
% 0.35/0.55      inference('sup+', [status(thm)], ['16', '19'])).
% 0.35/0.55  thf(commutativity_k5_xboole_0, axiom,
% 0.35/0.55    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.35/0.55  thf('21', plain,
% 0.35/0.55      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.35/0.55      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.35/0.55  thf('22', plain,
% 0.35/0.55      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.35/0.55      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.35/0.55  thf(t5_boole, axiom,
% 0.35/0.55    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.35/0.55  thf('23', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 0.35/0.55      inference('cnf', [status(esa)], [t5_boole])).
% 0.35/0.55  thf('24', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.35/0.55      inference('sup+', [status(thm)], ['22', '23'])).
% 0.35/0.55  thf('25', plain,
% 0.35/0.55      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))),
% 0.35/0.55      inference('demod', [status(thm)], ['20', '21', '24'])).
% 0.35/0.55  thf('26', plain,
% 0.35/0.55      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('27', plain, ($false),
% 0.35/0.55      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 0.35/0.55  
% 0.35/0.55  % SZS output end Refutation
% 0.35/0.55  
% 0.35/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
