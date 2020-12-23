%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ler23vixS7

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:58 EST 2020

% Result     : Theorem 10.87s
% Output     : Refutation 10.87s
% Verified   : 
% Statistics : Number of formulae       :   50 (  73 expanded)
%              Number of leaves         :   18 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :  457 ( 683 expanded)
%              Number of equality atoms :   38 (  61 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t47_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( k3_enumset1 @ A @ B @ C @ D @ E )
        = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ) ),
    inference('cnf.neg',[status(esa)],[t47_enumset1])).

thf('0',plain,(
    ( k3_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E )
 != ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_enumset1 @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_tarski @ X24 @ X25 )
      = ( k2_xboole_0 @ ( k1_tarski @ X24 ) @ ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k2_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t43_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ) )).

thf('6',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k1_enumset1 @ X26 @ X27 @ X28 )
      = ( k2_xboole_0 @ ( k2_tarski @ X26 @ X27 ) @ ( k1_tarski @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('7',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_tarski @ X24 @ X25 )
      = ( k2_xboole_0 @ ( k1_tarski @ X24 ) @ ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_tarski @ X24 @ X25 )
      = ( k2_xboole_0 @ ( k1_tarski @ X24 ) @ ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('10',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k1_enumset1 @ X26 @ X27 @ X28 )
      = ( k2_xboole_0 @ ( k2_tarski @ X26 @ X27 ) @ ( k1_tarski @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('11',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k2_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('14',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k2_enumset1 @ X29 @ X30 @ X31 @ X32 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X29 @ X30 @ X31 ) @ ( k1_tarski @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k1_enumset1 @ X1 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','15'])).

thf('17',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_tarski @ X24 @ X25 )
      = ( k2_xboole_0 @ ( k1_tarski @ X24 ) @ ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k1_enumset1 @ X26 @ X27 @ X28 )
      = ( k2_xboole_0 @ ( k2_tarski @ X26 @ X27 ) @ ( k1_tarski @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k2_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X3 @ X2 ) @ ( k1_enumset1 @ X1 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf(l57_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) )).

thf('26',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k3_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X19 @ X20 @ X21 ) @ ( k2_tarski @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X3 @ X2 ) @ ( k1_enumset1 @ X1 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,(
    ( k3_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E )
 != ( k3_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E ) ),
    inference(demod,[status(thm)],['0','28'])).

thf('30',plain,(
    $false ),
    inference(simplify,[status(thm)],['29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ler23vixS7
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:08:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 10.87/11.06  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 10.87/11.06  % Solved by: fo/fo7.sh
% 10.87/11.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 10.87/11.06  % done 7040 iterations in 10.636s
% 10.87/11.06  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 10.87/11.06  % SZS output start Refutation
% 10.87/11.06  thf(sk_A_type, type, sk_A: $i).
% 10.87/11.06  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 10.87/11.06  thf(sk_C_1_type, type, sk_C_1: $i).
% 10.87/11.06  thf(sk_E_type, type, sk_E: $i).
% 10.87/11.06  thf(sk_D_1_type, type, sk_D_1: $i).
% 10.87/11.06  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 10.87/11.06  thf(sk_B_type, type, sk_B: $i).
% 10.87/11.06  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 10.87/11.06  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 10.87/11.06  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 10.87/11.06  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 10.87/11.06  thf(t47_enumset1, conjecture,
% 10.87/11.06    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 10.87/11.06     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 10.87/11.06       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ))).
% 10.87/11.06  thf(zf_stmt_0, negated_conjecture,
% 10.87/11.06    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 10.87/11.06        ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 10.87/11.06          ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ) )),
% 10.87/11.06    inference('cnf.neg', [status(esa)], [t47_enumset1])).
% 10.87/11.06  thf('0', plain,
% 10.87/11.06      (((k3_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E)
% 10.87/11.06         != (k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 10.87/11.06             (k2_enumset1 @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E)))),
% 10.87/11.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.87/11.06  thf(idempotence_k2_xboole_0, axiom,
% 10.87/11.06    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 10.87/11.06  thf('1', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 10.87/11.06      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 10.87/11.06  thf(t41_enumset1, axiom,
% 10.87/11.06    (![A:$i,B:$i]:
% 10.87/11.06     ( ( k2_tarski @ A @ B ) =
% 10.87/11.06       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 10.87/11.06  thf('2', plain,
% 10.87/11.06      (![X24 : $i, X25 : $i]:
% 10.87/11.06         ((k2_tarski @ X24 @ X25)
% 10.87/11.06           = (k2_xboole_0 @ (k1_tarski @ X24) @ (k1_tarski @ X25)))),
% 10.87/11.06      inference('cnf', [status(esa)], [t41_enumset1])).
% 10.87/11.06  thf(t4_xboole_1, axiom,
% 10.87/11.06    (![A:$i,B:$i,C:$i]:
% 10.87/11.06     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 10.87/11.06       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 10.87/11.06  thf('3', plain,
% 10.87/11.06      (![X5 : $i, X6 : $i, X7 : $i]:
% 10.87/11.06         ((k2_xboole_0 @ (k2_xboole_0 @ X5 @ X6) @ X7)
% 10.87/11.06           = (k2_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 10.87/11.06      inference('cnf', [status(esa)], [t4_xboole_1])).
% 10.87/11.06  thf('4', plain,
% 10.87/11.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.87/11.06         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 10.87/11.06           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 10.87/11.06              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 10.87/11.06      inference('sup+', [status(thm)], ['2', '3'])).
% 10.87/11.06  thf('5', plain,
% 10.87/11.06      (![X0 : $i, X1 : $i]:
% 10.87/11.06         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0))
% 10.87/11.06           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 10.87/11.06      inference('sup+', [status(thm)], ['1', '4'])).
% 10.87/11.06  thf(t43_enumset1, axiom,
% 10.87/11.06    (![A:$i,B:$i,C:$i]:
% 10.87/11.06     ( ( k1_enumset1 @ A @ B @ C ) =
% 10.87/11.06       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ))).
% 10.87/11.06  thf('6', plain,
% 10.87/11.06      (![X26 : $i, X27 : $i, X28 : $i]:
% 10.87/11.06         ((k1_enumset1 @ X26 @ X27 @ X28)
% 10.87/11.06           = (k2_xboole_0 @ (k2_tarski @ X26 @ X27) @ (k1_tarski @ X28)))),
% 10.87/11.06      inference('cnf', [status(esa)], [t43_enumset1])).
% 10.87/11.06  thf('7', plain,
% 10.87/11.06      (![X24 : $i, X25 : $i]:
% 10.87/11.06         ((k2_tarski @ X24 @ X25)
% 10.87/11.06           = (k2_xboole_0 @ (k1_tarski @ X24) @ (k1_tarski @ X25)))),
% 10.87/11.06      inference('cnf', [status(esa)], [t41_enumset1])).
% 10.87/11.06  thf('8', plain,
% 10.87/11.06      (![X0 : $i, X1 : $i]:
% 10.87/11.06         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 10.87/11.06      inference('demod', [status(thm)], ['5', '6', '7'])).
% 10.87/11.06  thf('9', plain,
% 10.87/11.06      (![X24 : $i, X25 : $i]:
% 10.87/11.06         ((k2_tarski @ X24 @ X25)
% 10.87/11.06           = (k2_xboole_0 @ (k1_tarski @ X24) @ (k1_tarski @ X25)))),
% 10.87/11.06      inference('cnf', [status(esa)], [t41_enumset1])).
% 10.87/11.06  thf('10', plain,
% 10.87/11.06      (![X26 : $i, X27 : $i, X28 : $i]:
% 10.87/11.06         ((k1_enumset1 @ X26 @ X27 @ X28)
% 10.87/11.06           = (k2_xboole_0 @ (k2_tarski @ X26 @ X27) @ (k1_tarski @ X28)))),
% 10.87/11.06      inference('cnf', [status(esa)], [t43_enumset1])).
% 10.87/11.06  thf('11', plain,
% 10.87/11.06      (![X5 : $i, X6 : $i, X7 : $i]:
% 10.87/11.06         ((k2_xboole_0 @ (k2_xboole_0 @ X5 @ X6) @ X7)
% 10.87/11.06           = (k2_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 10.87/11.06      inference('cnf', [status(esa)], [t4_xboole_1])).
% 10.87/11.06  thf('12', plain,
% 10.87/11.06      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.87/11.06         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 10.87/11.06           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ 
% 10.87/11.06              (k2_xboole_0 @ (k1_tarski @ X0) @ X3)))),
% 10.87/11.06      inference('sup+', [status(thm)], ['10', '11'])).
% 10.87/11.06  thf('13', plain,
% 10.87/11.06      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.87/11.06         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 10.87/11.06           = (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0)))),
% 10.87/11.06      inference('sup+', [status(thm)], ['9', '12'])).
% 10.87/11.06  thf(t46_enumset1, axiom,
% 10.87/11.06    (![A:$i,B:$i,C:$i,D:$i]:
% 10.87/11.06     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 10.87/11.06       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 10.87/11.06  thf('14', plain,
% 10.87/11.06      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 10.87/11.06         ((k2_enumset1 @ X29 @ X30 @ X31 @ X32)
% 10.87/11.06           = (k2_xboole_0 @ (k1_enumset1 @ X29 @ X30 @ X31) @ (k1_tarski @ X32)))),
% 10.87/11.06      inference('cnf', [status(esa)], [t46_enumset1])).
% 10.87/11.06  thf('15', plain,
% 10.87/11.06      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.87/11.06         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 10.87/11.06           = (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0)))),
% 10.87/11.06      inference('demod', [status(thm)], ['13', '14'])).
% 10.87/11.06  thf('16', plain,
% 10.87/11.06      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.87/11.06         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 10.87/11.06           = (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ 
% 10.87/11.06              (k1_enumset1 @ X1 @ X0 @ X0)))),
% 10.87/11.06      inference('sup+', [status(thm)], ['8', '15'])).
% 10.87/11.06  thf('17', plain,
% 10.87/11.06      (![X24 : $i, X25 : $i]:
% 10.87/11.06         ((k2_tarski @ X24 @ X25)
% 10.87/11.06           = (k2_xboole_0 @ (k1_tarski @ X24) @ (k1_tarski @ X25)))),
% 10.87/11.06      inference('cnf', [status(esa)], [t41_enumset1])).
% 10.87/11.06  thf('18', plain,
% 10.87/11.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.87/11.06         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 10.87/11.06           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 10.87/11.06              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 10.87/11.06      inference('sup+', [status(thm)], ['2', '3'])).
% 10.87/11.06  thf('19', plain,
% 10.87/11.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.87/11.06         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 10.87/11.06           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 10.87/11.06      inference('sup+', [status(thm)], ['17', '18'])).
% 10.87/11.06  thf('20', plain,
% 10.87/11.06      (![X26 : $i, X27 : $i, X28 : $i]:
% 10.87/11.06         ((k1_enumset1 @ X26 @ X27 @ X28)
% 10.87/11.06           = (k2_xboole_0 @ (k2_tarski @ X26 @ X27) @ (k1_tarski @ X28)))),
% 10.87/11.06      inference('cnf', [status(esa)], [t43_enumset1])).
% 10.87/11.06  thf('21', plain,
% 10.87/11.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.87/11.06         ((k1_enumset1 @ X2 @ X1 @ X0)
% 10.87/11.06           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 10.87/11.06      inference('sup+', [status(thm)], ['19', '20'])).
% 10.87/11.06  thf('22', plain,
% 10.87/11.06      (![X5 : $i, X6 : $i, X7 : $i]:
% 10.87/11.06         ((k2_xboole_0 @ (k2_xboole_0 @ X5 @ X6) @ X7)
% 10.87/11.06           = (k2_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 10.87/11.06      inference('cnf', [status(esa)], [t4_xboole_1])).
% 10.87/11.06  thf('23', plain,
% 10.87/11.06      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.87/11.06         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 10.87/11.06           = (k2_xboole_0 @ (k1_tarski @ X2) @ 
% 10.87/11.06              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X3)))),
% 10.87/11.06      inference('sup+', [status(thm)], ['21', '22'])).
% 10.87/11.06  thf('24', plain,
% 10.87/11.06      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 10.87/11.06         ((k2_xboole_0 @ (k1_enumset1 @ X4 @ X3 @ X2) @ 
% 10.87/11.06           (k1_enumset1 @ X1 @ X0 @ X0))
% 10.87/11.06           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 10.87/11.06              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 10.87/11.06      inference('sup+', [status(thm)], ['16', '23'])).
% 10.87/11.06  thf('25', plain,
% 10.87/11.06      (![X0 : $i, X1 : $i]:
% 10.87/11.06         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 10.87/11.06      inference('demod', [status(thm)], ['5', '6', '7'])).
% 10.87/11.06  thf(l57_enumset1, axiom,
% 10.87/11.06    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 10.87/11.06     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 10.87/11.06       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ))).
% 10.87/11.06  thf('26', plain,
% 10.87/11.06      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 10.87/11.06         ((k3_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23)
% 10.87/11.06           = (k2_xboole_0 @ (k1_enumset1 @ X19 @ X20 @ X21) @ 
% 10.87/11.06              (k2_tarski @ X22 @ X23)))),
% 10.87/11.06      inference('cnf', [status(esa)], [l57_enumset1])).
% 10.87/11.06  thf('27', plain,
% 10.87/11.06      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 10.87/11.06         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 10.87/11.06           = (k2_xboole_0 @ (k1_enumset1 @ X4 @ X3 @ X2) @ 
% 10.87/11.06              (k1_enumset1 @ X1 @ X0 @ X0)))),
% 10.87/11.06      inference('sup+', [status(thm)], ['25', '26'])).
% 10.87/11.06  thf('28', plain,
% 10.87/11.06      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 10.87/11.06         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 10.87/11.06           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 10.87/11.06              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 10.87/11.06      inference('demod', [status(thm)], ['24', '27'])).
% 10.87/11.06  thf('29', plain,
% 10.87/11.06      (((k3_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E)
% 10.87/11.06         != (k3_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E))),
% 10.87/11.06      inference('demod', [status(thm)], ['0', '28'])).
% 10.87/11.06  thf('30', plain, ($false), inference('simplify', [status(thm)], ['29'])).
% 10.87/11.06  
% 10.87/11.06  % SZS output end Refutation
% 10.87/11.06  
% 10.87/11.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
