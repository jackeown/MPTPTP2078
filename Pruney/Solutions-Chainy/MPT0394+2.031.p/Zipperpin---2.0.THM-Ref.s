%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.B4cJZvvYqj

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:48 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   50 (  71 expanded)
%              Number of leaves         :   22 (  30 expanded)
%              Depth                    :   12
%              Number of atoms          :  308 ( 452 expanded)
%              Number of equality atoms :   46 (  66 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t12_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
        = ( k3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_setfam_1])).

thf('0',plain,(
    ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_tarski @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k1_tarski @ X13 ) @ ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('2',plain,(
    ! [X21: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf(t10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) )
         != ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) )).

thf('3',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ X19 @ X20 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X19 ) @ ( k1_setfam_1 @ X20 ) ) )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t10_setfam_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ ( k1_setfam_1 @ X1 ) ) )
      | ( X1 = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('5',plain,(
    ! [X3: $i] :
      ( r1_xboole_0 @ X3 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k3_xboole_0 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('12',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ( ( k4_xboole_0 @ X17 @ ( k1_tarski @ X16 ) )
       != X17 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('14',plain,(
    ! [X15: $i] :
      ( ( k2_tarski @ X15 @ X15 )
      = ( k1_tarski @ X15 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X8 != X7 )
      | ( r2_hidden @ X8 @ X9 )
      | ( X9
       != ( k2_tarski @ X10 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('16',plain,(
    ! [X7: $i,X10: $i] :
      ( r2_hidden @ X7 @ ( k2_tarski @ X10 @ X7 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['13','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ ( k1_setfam_1 @ X1 ) ) ) ) ),
    inference(clc,[status(thm)],['4','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','19'])).

thf('21',plain,(
    ! [X21: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['13','17'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','24'])).

thf('26',plain,(
    $false ),
    inference(simplify,[status(thm)],['25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.B4cJZvvYqj
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:15:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 67 iterations in 0.023s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.52  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.22/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.52  thf(t12_setfam_1, conjecture,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i,B:$i]:
% 0.22/0.52        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t12_setfam_1])).
% 0.22/0.52  thf('0', plain,
% 0.22/0.52      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.22/0.52         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t41_enumset1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( k2_tarski @ A @ B ) =
% 0.22/0.52       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      (![X13 : $i, X14 : $i]:
% 0.22/0.52         ((k2_tarski @ X13 @ X14)
% 0.22/0.52           = (k2_xboole_0 @ (k1_tarski @ X13) @ (k1_tarski @ X14)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.22/0.52  thf(t11_setfam_1, axiom,
% 0.22/0.52    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.22/0.52  thf('2', plain, (![X21 : $i]: ((k1_setfam_1 @ (k1_tarski @ X21)) = (X21))),
% 0.22/0.52      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.22/0.52  thf(t10_setfam_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.52          ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) ) !=
% 0.22/0.52            ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) ))).
% 0.22/0.52  thf('3', plain,
% 0.22/0.52      (![X19 : $i, X20 : $i]:
% 0.22/0.52         (((X19) = (k1_xboole_0))
% 0.22/0.52          | ((k1_setfam_1 @ (k2_xboole_0 @ X19 @ X20))
% 0.22/0.52              = (k3_xboole_0 @ (k1_setfam_1 @ X19) @ (k1_setfam_1 @ X20)))
% 0.22/0.52          | ((X20) = (k1_xboole_0)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t10_setfam_1])).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (((k1_setfam_1 @ (k2_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.22/0.52            = (k3_xboole_0 @ X0 @ (k1_setfam_1 @ X1)))
% 0.22/0.52          | ((X1) = (k1_xboole_0))
% 0.22/0.52          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['2', '3'])).
% 0.22/0.52  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.22/0.52  thf('5', plain, (![X3 : $i]: (r1_xboole_0 @ X3 @ k1_xboole_0)),
% 0.22/0.52      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.22/0.52  thf(t83_xboole_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.52  thf('6', plain,
% 0.22/0.52      (![X4 : $i, X5 : $i]:
% 0.22/0.52         (((k4_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.22/0.52      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.22/0.52  thf('7', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.52  thf(t48_xboole_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      (![X1 : $i, X2 : $i]:
% 0.22/0.52         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X2))
% 0.22/0.52           = (k3_xboole_0 @ X1 @ X2))),
% 0.22/0.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.52  thf('9', plain,
% 0.22/0.52      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['7', '8'])).
% 0.22/0.52  thf(t2_boole, axiom,
% 0.22/0.52    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.52  thf('10', plain,
% 0.22/0.52      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.52      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.52  thf('11', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.52      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.52  thf(t65_zfmisc_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.22/0.52       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.22/0.52  thf('12', plain,
% 0.22/0.52      (![X16 : $i, X17 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X16 @ X17)
% 0.22/0.52          | ((k4_xboole_0 @ X17 @ (k1_tarski @ X16)) != (X17)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.22/0.52          | ~ (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.52  thf(t69_enumset1, axiom,
% 0.22/0.52    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.52  thf('14', plain,
% 0.22/0.52      (![X15 : $i]: ((k2_tarski @ X15 @ X15) = (k1_tarski @ X15))),
% 0.22/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.52  thf(d2_tarski, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.22/0.52       ( ![D:$i]:
% 0.22/0.52         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.52         (((X8) != (X7))
% 0.22/0.52          | (r2_hidden @ X8 @ X9)
% 0.22/0.52          | ((X9) != (k2_tarski @ X10 @ X7)))),
% 0.22/0.52      inference('cnf', [status(esa)], [d2_tarski])).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      (![X7 : $i, X10 : $i]: (r2_hidden @ X7 @ (k2_tarski @ X10 @ X7))),
% 0.22/0.52      inference('simplify', [status(thm)], ['15'])).
% 0.22/0.52  thf('17', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['14', '16'])).
% 0.22/0.52  thf('18', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.22/0.52      inference('demod', [status(thm)], ['13', '17'])).
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (((X1) = (k1_xboole_0))
% 0.22/0.52          | ((k1_setfam_1 @ (k2_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.22/0.52              = (k3_xboole_0 @ X0 @ (k1_setfam_1 @ X1))))),
% 0.22/0.52      inference('clc', [status(thm)], ['4', '18'])).
% 0.22/0.52  thf('20', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.22/0.52            = (k3_xboole_0 @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0))))
% 0.22/0.52          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['1', '19'])).
% 0.22/0.52  thf('21', plain, (![X21 : $i]: ((k1_setfam_1 @ (k1_tarski @ X21)) = (X21))),
% 0.22/0.52      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.22/0.52  thf('22', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))
% 0.22/0.52          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.22/0.52      inference('demod', [status(thm)], ['20', '21'])).
% 0.22/0.52  thf('23', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.22/0.52      inference('demod', [status(thm)], ['13', '17'])).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))),
% 0.22/0.52      inference('clc', [status(thm)], ['22', '23'])).
% 0.22/0.52  thf('25', plain,
% 0.22/0.52      (((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['0', '24'])).
% 0.22/0.52  thf('26', plain, ($false), inference('simplify', [status(thm)], ['25'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
