%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.n3VVq6BB04

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:55 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   51 (  68 expanded)
%              Number of leaves         :   20 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :  352 ( 481 expanded)
%              Number of equality atoms :   21 (  25 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X19: $i] :
      ( ( k3_xboole_0 @ X19 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t25_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ B @ C ) ) @ ( k3_xboole_0 @ C @ A ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ B @ C ) ) @ ( k2_xboole_0 @ C @ A ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k3_xboole_0 @ X17 @ X18 ) ) @ ( k3_xboole_0 @ X18 @ X16 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ ( k2_xboole_0 @ X17 @ X18 ) ) @ ( k2_xboole_0 @ X18 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t25_xboole_1])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('4',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k3_xboole_0 @ X17 @ X18 ) ) @ ( k3_xboole_0 @ X18 @ X16 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ X17 @ X18 ) @ ( k2_xboole_0 @ X18 @ X16 ) ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X1 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('7',plain,(
    ! [X21: $i] :
      ( ( X21 = k1_xboole_0 )
      | ~ ( r1_tarski @ X21 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('9',plain,(
    ! [X20: $i] :
      ( r1_tarski @ k1_xboole_0 @ X20 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X10: $i] :
      ( ( k2_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','8','11','12','13','14','15'])).

thf('17',plain,(
    r1_tarski @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('19',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_tarski @ X12 @ X13 )
      | ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_C @ X0 ) @ sk_D ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_D ) ),
    inference('sup+',[status(thm)],['16','21'])).

thf('23',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('26',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X7 @ X9 )
      | ( r1_tarski @ X7 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k3_xboole_0 @ sk_B @ X1 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['0','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.n3VVq6BB04
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:42:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.43/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.43/0.60  % Solved by: fo/fo7.sh
% 0.43/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.60  % done 326 iterations in 0.141s
% 0.43/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.43/0.60  % SZS output start Refutation
% 0.43/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.43/0.60  thf(sk_D_type, type, sk_D: $i).
% 0.43/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.43/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.43/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.43/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.60  thf(t27_xboole_1, conjecture,
% 0.43/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.60     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.43/0.60       ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ ( k3_xboole_0 @ B @ D ) ) ))).
% 0.43/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.60    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.60        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.43/0.60          ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ ( k3_xboole_0 @ B @ D ) ) ) )),
% 0.43/0.60    inference('cnf.neg', [status(esa)], [t27_xboole_1])).
% 0.43/0.60  thf('0', plain,
% 0.43/0.60      (~ (r1_tarski @ (k3_xboole_0 @ sk_A @ sk_C) @ (k3_xboole_0 @ sk_B @ sk_D))),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf(t2_boole, axiom,
% 0.43/0.60    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.43/0.60  thf('1', plain,
% 0.43/0.60      (![X19 : $i]: ((k3_xboole_0 @ X19 @ k1_xboole_0) = (k1_xboole_0))),
% 0.43/0.60      inference('cnf', [status(esa)], [t2_boole])).
% 0.43/0.60  thf(t25_xboole_1, axiom,
% 0.43/0.60    (![A:$i,B:$i,C:$i]:
% 0.43/0.60     ( ( k2_xboole_0 @
% 0.43/0.60         ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ B @ C ) ) @ 
% 0.43/0.60         ( k3_xboole_0 @ C @ A ) ) =
% 0.43/0.60       ( k3_xboole_0 @
% 0.43/0.60         ( k3_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ B @ C ) ) @ 
% 0.43/0.60         ( k2_xboole_0 @ C @ A ) ) ))).
% 0.43/0.60  thf('2', plain,
% 0.43/0.60      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.43/0.60         ((k2_xboole_0 @ 
% 0.43/0.60           (k2_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ (k3_xboole_0 @ X17 @ X18)) @ 
% 0.43/0.60           (k3_xboole_0 @ X18 @ X16))
% 0.43/0.60           = (k3_xboole_0 @ 
% 0.43/0.60              (k3_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ 
% 0.43/0.60               (k2_xboole_0 @ X17 @ X18)) @ 
% 0.43/0.60              (k2_xboole_0 @ X18 @ X16)))),
% 0.43/0.60      inference('cnf', [status(esa)], [t25_xboole_1])).
% 0.43/0.60  thf(t16_xboole_1, axiom,
% 0.43/0.60    (![A:$i,B:$i,C:$i]:
% 0.43/0.60     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.43/0.60       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.43/0.60  thf('3', plain,
% 0.43/0.60      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.43/0.60         ((k3_xboole_0 @ (k3_xboole_0 @ X2 @ X3) @ X4)
% 0.43/0.60           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.43/0.60      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.43/0.60  thf('4', plain,
% 0.43/0.60      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.43/0.60         ((k2_xboole_0 @ 
% 0.43/0.60           (k2_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ (k3_xboole_0 @ X17 @ X18)) @ 
% 0.43/0.60           (k3_xboole_0 @ X18 @ X16))
% 0.43/0.60           = (k3_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ 
% 0.43/0.60              (k3_xboole_0 @ (k2_xboole_0 @ X17 @ X18) @ 
% 0.43/0.60               (k2_xboole_0 @ X18 @ X16))))),
% 0.43/0.60      inference('demod', [status(thm)], ['2', '3'])).
% 0.43/0.60  thf('5', plain,
% 0.43/0.60      (![X0 : $i, X1 : $i]:
% 0.43/0.60         ((k2_xboole_0 @ 
% 0.43/0.60           (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X1)) @ 
% 0.43/0.60           (k3_xboole_0 @ X1 @ X0))
% 0.43/0.60           = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ 
% 0.43/0.60              (k3_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X1) @ 
% 0.43/0.60               (k2_xboole_0 @ X1 @ X0))))),
% 0.43/0.60      inference('sup+', [status(thm)], ['1', '4'])).
% 0.43/0.60  thf(t17_xboole_1, axiom,
% 0.43/0.60    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.43/0.60  thf('6', plain,
% 0.43/0.60      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 0.43/0.60      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.43/0.60  thf(t3_xboole_1, axiom,
% 0.43/0.60    (![A:$i]:
% 0.43/0.60     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.43/0.60  thf('7', plain,
% 0.43/0.60      (![X21 : $i]:
% 0.43/0.60         (((X21) = (k1_xboole_0)) | ~ (r1_tarski @ X21 @ k1_xboole_0))),
% 0.43/0.60      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.43/0.60  thf('8', plain,
% 0.43/0.60      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.43/0.60      inference('sup-', [status(thm)], ['6', '7'])).
% 0.43/0.60  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.43/0.60  thf('9', plain, (![X20 : $i]: (r1_tarski @ k1_xboole_0 @ X20)),
% 0.43/0.60      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.43/0.60  thf(t12_xboole_1, axiom,
% 0.43/0.60    (![A:$i,B:$i]:
% 0.43/0.60     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.43/0.60  thf('10', plain,
% 0.43/0.60      (![X0 : $i, X1 : $i]:
% 0.43/0.60         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 0.43/0.60      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.43/0.60  thf('11', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.43/0.60      inference('sup-', [status(thm)], ['9', '10'])).
% 0.43/0.60  thf('12', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.43/0.60      inference('sup-', [status(thm)], ['9', '10'])).
% 0.43/0.60  thf(t1_boole, axiom,
% 0.43/0.60    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.43/0.60  thf('13', plain, (![X10 : $i]: ((k2_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.43/0.60      inference('cnf', [status(esa)], [t1_boole])).
% 0.43/0.60  thf('14', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.43/0.60      inference('sup-', [status(thm)], ['9', '10'])).
% 0.43/0.60  thf(t21_xboole_1, axiom,
% 0.43/0.60    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.43/0.60  thf('15', plain,
% 0.43/0.60      (![X14 : $i, X15 : $i]:
% 0.43/0.60         ((k3_xboole_0 @ X14 @ (k2_xboole_0 @ X14 @ X15)) = (X14))),
% 0.43/0.60      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.43/0.60  thf('16', plain,
% 0.43/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.43/0.60      inference('demod', [status(thm)],
% 0.43/0.60                ['5', '8', '11', '12', '13', '14', '15'])).
% 0.43/0.60  thf('17', plain, ((r1_tarski @ sk_C @ sk_D)),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('18', plain,
% 0.43/0.60      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 0.43/0.60      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.43/0.60  thf(t1_xboole_1, axiom,
% 0.43/0.60    (![A:$i,B:$i,C:$i]:
% 0.43/0.60     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.43/0.60       ( r1_tarski @ A @ C ) ))).
% 0.43/0.60  thf('19', plain,
% 0.43/0.60      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.43/0.60         (~ (r1_tarski @ X11 @ X12)
% 0.43/0.60          | ~ (r1_tarski @ X12 @ X13)
% 0.43/0.60          | (r1_tarski @ X11 @ X13))),
% 0.43/0.60      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.43/0.60  thf('20', plain,
% 0.43/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.60         ((r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.43/0.60      inference('sup-', [status(thm)], ['18', '19'])).
% 0.43/0.60  thf('21', plain,
% 0.43/0.60      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ sk_C @ X0) @ sk_D)),
% 0.43/0.60      inference('sup-', [status(thm)], ['17', '20'])).
% 0.43/0.60  thf('22', plain,
% 0.43/0.60      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C) @ sk_D)),
% 0.43/0.60      inference('sup+', [status(thm)], ['16', '21'])).
% 0.43/0.60  thf('23', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('24', plain,
% 0.43/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.60         ((r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.43/0.60      inference('sup-', [status(thm)], ['18', '19'])).
% 0.43/0.60  thf('25', plain,
% 0.43/0.60      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ sk_B)),
% 0.43/0.60      inference('sup-', [status(thm)], ['23', '24'])).
% 0.43/0.60  thf(t19_xboole_1, axiom,
% 0.43/0.60    (![A:$i,B:$i,C:$i]:
% 0.43/0.60     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.43/0.60       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.43/0.60  thf('26', plain,
% 0.43/0.60      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.43/0.60         (~ (r1_tarski @ X7 @ X8)
% 0.43/0.60          | ~ (r1_tarski @ X7 @ X9)
% 0.43/0.60          | (r1_tarski @ X7 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.43/0.60      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.43/0.60  thf('27', plain,
% 0.43/0.60      (![X0 : $i, X1 : $i]:
% 0.43/0.60         ((r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ (k3_xboole_0 @ sk_B @ X1))
% 0.43/0.60          | ~ (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ X1))),
% 0.43/0.60      inference('sup-', [status(thm)], ['25', '26'])).
% 0.43/0.60  thf('28', plain,
% 0.43/0.60      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_C) @ (k3_xboole_0 @ sk_B @ sk_D))),
% 0.43/0.60      inference('sup-', [status(thm)], ['22', '27'])).
% 0.43/0.60  thf('29', plain, ($false), inference('demod', [status(thm)], ['0', '28'])).
% 0.43/0.60  
% 0.43/0.60  % SZS output end Refutation
% 0.43/0.60  
% 0.43/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
