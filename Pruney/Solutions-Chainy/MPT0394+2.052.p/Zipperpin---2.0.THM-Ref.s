%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Z2Fd27Mhzx

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:51 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   49 (  88 expanded)
%              Number of leaves         :   20 (  35 expanded)
%              Depth                    :   12
%              Number of atoms          :  323 ( 670 expanded)
%              Number of equality atoms :   44 (  92 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X17 @ X17 @ X18 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k2_enumset1 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X7 @ X8 @ X9 ) @ ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('4',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k2_enumset1 @ X19 @ X19 @ X20 @ X21 )
      = ( k1_enumset1 @ X19 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('5',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X17 @ X17 @ X18 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','7'])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('9',plain,(
    ! [X28: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X28 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf(t10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) )
         != ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) )).

thf('10',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X26 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ X26 @ X27 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X26 ) @ ( k1_setfam_1 @ X27 ) ) )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t10_setfam_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X1 ) @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ ( k1_tarski @ X1 ) ) @ X0 ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X28: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X28 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t12_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
        = ( k3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_setfam_1])).

thf('15',plain,(
    ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
     != ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t16_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        & ( A = B ) ) )).

thf('18',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X24 ) @ ( k1_tarski @ X25 ) )
      | ( X24 != X25 ) ) ),
    inference(cnf,[status(esa)],[t16_zfmisc_1])).

thf('19',plain,(
    ! [X25: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X25 ) @ ( k1_tarski @ X25 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ~ ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('21',plain,(
    ! [X3: $i] :
      ( r1_xboole_0 @ X3 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('22',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X25: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X25 ) @ ( k1_tarski @ X25 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('24',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','21'])).

thf('26',plain,(
    ! [X3: $i] :
      ( r1_xboole_0 @ X3 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['24','25','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Z2Fd27Mhzx
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:40:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.40/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.61  % Solved by: fo/fo7.sh
% 0.40/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.61  % done 411 iterations in 0.158s
% 0.40/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.61  % SZS output start Refutation
% 0.40/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.40/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.61  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.40/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.40/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.61  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.40/0.61  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.40/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.61  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.40/0.61  thf(t69_enumset1, axiom,
% 0.40/0.61    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.40/0.61  thf('0', plain, (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.40/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.40/0.61  thf(t70_enumset1, axiom,
% 0.40/0.61    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.40/0.61  thf('1', plain,
% 0.40/0.61      (![X17 : $i, X18 : $i]:
% 0.40/0.61         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 0.40/0.61      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.40/0.61  thf(t46_enumset1, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.61     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.40/0.61       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.40/0.61  thf('2', plain,
% 0.40/0.61      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.40/0.61         ((k2_enumset1 @ X7 @ X8 @ X9 @ X10)
% 0.40/0.61           = (k2_xboole_0 @ (k1_enumset1 @ X7 @ X8 @ X9) @ (k1_tarski @ X10)))),
% 0.40/0.61      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.40/0.61  thf('3', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.61         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.40/0.61           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.40/0.61      inference('sup+', [status(thm)], ['1', '2'])).
% 0.40/0.61  thf(t71_enumset1, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.40/0.61  thf('4', plain,
% 0.40/0.61      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.40/0.61         ((k2_enumset1 @ X19 @ X19 @ X20 @ X21)
% 0.40/0.61           = (k1_enumset1 @ X19 @ X20 @ X21))),
% 0.40/0.61      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.40/0.61  thf('5', plain,
% 0.40/0.61      (![X17 : $i, X18 : $i]:
% 0.40/0.61         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 0.40/0.61      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.40/0.61  thf('6', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.40/0.61      inference('sup+', [status(thm)], ['4', '5'])).
% 0.40/0.61  thf('7', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         ((k2_xboole_0 @ (k2_tarski @ X1 @ X1) @ (k1_tarski @ X0))
% 0.40/0.61           = (k2_tarski @ X1 @ X0))),
% 0.40/0.61      inference('sup+', [status(thm)], ['3', '6'])).
% 0.40/0.61  thf('8', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.40/0.61           = (k2_tarski @ X0 @ X1))),
% 0.40/0.61      inference('sup+', [status(thm)], ['0', '7'])).
% 0.40/0.61  thf(t11_setfam_1, axiom,
% 0.40/0.61    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.40/0.61  thf('9', plain, (![X28 : $i]: ((k1_setfam_1 @ (k1_tarski @ X28)) = (X28))),
% 0.40/0.61      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.40/0.61  thf(t10_setfam_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.40/0.61          ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) ) !=
% 0.40/0.61            ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) ))).
% 0.40/0.61  thf('10', plain,
% 0.40/0.61      (![X26 : $i, X27 : $i]:
% 0.40/0.61         (((X26) = (k1_xboole_0))
% 0.40/0.61          | ((k1_setfam_1 @ (k2_xboole_0 @ X26 @ X27))
% 0.40/0.61              = (k3_xboole_0 @ (k1_setfam_1 @ X26) @ (k1_setfam_1 @ X27)))
% 0.40/0.61          | ((X27) = (k1_xboole_0)))),
% 0.40/0.61      inference('cnf', [status(esa)], [t10_setfam_1])).
% 0.40/0.61  thf('11', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         (((k1_setfam_1 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.40/0.61            = (k3_xboole_0 @ (k1_setfam_1 @ X1) @ X0))
% 0.40/0.61          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.40/0.61          | ((X1) = (k1_xboole_0)))),
% 0.40/0.61      inference('sup+', [status(thm)], ['9', '10'])).
% 0.40/0.61  thf('12', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.40/0.61            = (k3_xboole_0 @ (k1_setfam_1 @ (k1_tarski @ X1)) @ X0))
% 0.40/0.61          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.40/0.61          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.40/0.61      inference('sup+', [status(thm)], ['8', '11'])).
% 0.40/0.61  thf('13', plain, (![X28 : $i]: ((k1_setfam_1 @ (k1_tarski @ X28)) = (X28))),
% 0.40/0.61      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.40/0.61  thf('14', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))
% 0.40/0.61          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.40/0.61          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.40/0.61      inference('demod', [status(thm)], ['12', '13'])).
% 0.40/0.61  thf(t12_setfam_1, conjecture,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.40/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.61    (~( ![A:$i,B:$i]:
% 0.40/0.61        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ) )),
% 0.40/0.61    inference('cnf.neg', [status(esa)], [t12_setfam_1])).
% 0.40/0.61  thf('15', plain,
% 0.40/0.61      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.40/0.61         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('16', plain,
% 0.40/0.61      ((((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))
% 0.40/0.61        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.40/0.61        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['14', '15'])).
% 0.40/0.61  thf('17', plain,
% 0.40/0.61      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.40/0.61        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.40/0.61      inference('simplify', [status(thm)], ['16'])).
% 0.40/0.61  thf(t16_zfmisc_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) & 
% 0.40/0.61          ( ( A ) = ( B ) ) ) ))).
% 0.40/0.61  thf('18', plain,
% 0.40/0.61      (![X24 : $i, X25 : $i]:
% 0.40/0.61         (~ (r1_xboole_0 @ (k1_tarski @ X24) @ (k1_tarski @ X25))
% 0.40/0.61          | ((X24) != (X25)))),
% 0.40/0.61      inference('cnf', [status(esa)], [t16_zfmisc_1])).
% 0.40/0.61  thf('19', plain,
% 0.40/0.61      (![X25 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X25) @ (k1_tarski @ X25))),
% 0.40/0.61      inference('simplify', [status(thm)], ['18'])).
% 0.40/0.61  thf('20', plain,
% 0.40/0.61      ((~ (r1_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0)
% 0.40/0.61        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['17', '19'])).
% 0.40/0.61  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.40/0.61  thf('21', plain, (![X3 : $i]: (r1_xboole_0 @ X3 @ k1_xboole_0)),
% 0.40/0.61      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.40/0.61  thf('22', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.40/0.61      inference('demod', [status(thm)], ['20', '21'])).
% 0.40/0.61  thf('23', plain,
% 0.40/0.61      (![X25 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X25) @ (k1_tarski @ X25))),
% 0.40/0.61      inference('simplify', [status(thm)], ['18'])).
% 0.40/0.61  thf('24', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)),
% 0.40/0.61      inference('sup-', [status(thm)], ['22', '23'])).
% 0.40/0.61  thf('25', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.40/0.61      inference('demod', [status(thm)], ['20', '21'])).
% 0.40/0.61  thf('26', plain, (![X3 : $i]: (r1_xboole_0 @ X3 @ k1_xboole_0)),
% 0.40/0.61      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.40/0.61  thf('27', plain, ($false),
% 0.40/0.61      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.40/0.61  
% 0.40/0.61  % SZS output end Refutation
% 0.40/0.61  
% 0.40/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
