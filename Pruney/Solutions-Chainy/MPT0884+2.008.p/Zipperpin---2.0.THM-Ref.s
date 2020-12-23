%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vXLkKTcmSX

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:25 EST 2020

% Result     : Theorem 6.24s
% Output     : Refutation 6.24s
% Verified   : 
% Statistics : Number of formulae       :   50 (  57 expanded)
%              Number of leaves         :   22 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :  550 ( 618 expanded)
%              Number of equality atoms :   36 (  43 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t44_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) @ ( k2_tarski @ D @ E ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ B @ C @ D ) @ ( k3_mcart_1 @ A @ C @ E ) @ ( k3_mcart_1 @ B @ C @ E ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( k3_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) @ ( k2_tarski @ D @ E ) )
        = ( k2_enumset1 @ ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ B @ C @ D ) @ ( k3_mcart_1 @ A @ C @ E ) @ ( k3_mcart_1 @ B @ C @ E ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_mcart_1])).

thf('0',plain,(
    ( k3_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) )
 != ( k2_enumset1 @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_D ) @ ( k3_mcart_1 @ sk_B @ sk_C @ sk_D ) @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_E ) @ ( k3_mcart_1 @ sk_B @ sk_C @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t43_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k1_enumset1 @ X2 @ X3 @ X4 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X3 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k1_enumset1 @ X2 @ X3 @ X4 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X3 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X2 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k2_enumset1 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k1_enumset1 @ X6 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X1 @ X2 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k2_enumset1 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k1_enumset1 @ X6 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X1 @ X2 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ( k3_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) )
 != ( k2_enumset1 @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_D ) @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_E ) @ ( k3_mcart_1 @ sk_B @ sk_C @ sk_D ) @ ( k3_mcart_1 @ sk_B @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['0','9'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('11',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k3_mcart_1 @ X22 @ X23 @ X24 )
      = ( k4_tarski @ ( k4_tarski @ X22 @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('12',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k3_mcart_1 @ X22 @ X23 @ X24 )
      = ( k4_tarski @ ( k4_tarski @ X22 @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(t146_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
      = ( k2_enumset1 @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X14 @ X17 ) @ ( k2_tarski @ X15 @ X16 ) )
      = ( k2_enumset1 @ ( k4_tarski @ X14 @ X15 ) @ ( k4_tarski @ X14 @ X16 ) @ ( k4_tarski @ X17 @ X15 ) @ ( k4_tarski @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t146_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X2 @ X1 ) @ X4 ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k4_tarski @ ( k4_tarski @ X2 @ X1 ) @ X3 ) @ ( k4_tarski @ X4 @ X0 ) @ ( k4_tarski @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k3_mcart_1 @ X22 @ X23 @ X24 )
      = ( k4_tarski @ ( k4_tarski @ X22 @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X2 @ X1 ) @ X4 ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k3_mcart_1 @ X2 @ X1 @ X3 ) @ ( k4_tarski @ X4 @ X0 ) @ ( k4_tarski @ X4 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X5 @ X4 ) @ ( k4_tarski @ X2 @ X1 ) ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ X5 @ X4 @ X0 ) @ ( k3_mcart_1 @ X5 @ X4 @ X3 ) @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k4_tarski @ ( k4_tarski @ X2 @ X1 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k3_mcart_1 @ X22 @ X23 @ X24 )
      = ( k4_tarski @ ( k4_tarski @ X22 @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X5 @ X4 ) @ ( k4_tarski @ X2 @ X1 ) ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ X5 @ X4 @ X0 ) @ ( k3_mcart_1 @ X5 @ X4 @ X3 ) @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k3_mcart_1 @ X2 @ X1 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('20',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X18 @ X19 ) @ ( k1_tarski @ X21 ) )
      = ( k2_tarski @ ( k4_tarski @ X18 @ X21 ) @ ( k4_tarski @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_tarski @ ( k4_tarski @ X1 @ X0 ) @ ( k4_tarski @ X2 @ X0 ) )
      = ( k2_zfmisc_1 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('24',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k3_zfmisc_1 @ X25 @ X26 @ X27 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('25',plain,(
    ( k3_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) )
 != ( k3_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) ) ),
    inference(demod,[status(thm)],['10','19','22','23','24'])).

thf('26',plain,(
    $false ),
    inference(simplify,[status(thm)],['25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vXLkKTcmSX
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:58:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 6.24/6.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.24/6.48  % Solved by: fo/fo7.sh
% 6.24/6.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.24/6.48  % done 3393 iterations in 6.023s
% 6.24/6.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.24/6.48  % SZS output start Refutation
% 6.24/6.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 6.24/6.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.24/6.48  thf(sk_E_type, type, sk_E: $i).
% 6.24/6.48  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 6.24/6.48  thf(sk_D_type, type, sk_D: $i).
% 6.24/6.48  thf(sk_A_type, type, sk_A: $i).
% 6.24/6.48  thf(sk_C_type, type, sk_C: $i).
% 6.24/6.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 6.24/6.48  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 6.24/6.48  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 6.24/6.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 6.24/6.48  thf(sk_B_type, type, sk_B: $i).
% 6.24/6.48  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 6.24/6.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 6.24/6.48  thf(t44_mcart_1, conjecture,
% 6.24/6.48    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 6.24/6.48     ( ( k3_zfmisc_1 @
% 6.24/6.48         ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) @ ( k2_tarski @ D @ E ) ) =
% 6.24/6.48       ( k2_enumset1 @
% 6.24/6.48         ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ B @ C @ D ) @ 
% 6.24/6.48         ( k3_mcart_1 @ A @ C @ E ) @ ( k3_mcart_1 @ B @ C @ E ) ) ))).
% 6.24/6.48  thf(zf_stmt_0, negated_conjecture,
% 6.24/6.48    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 6.24/6.48        ( ( k3_zfmisc_1 @
% 6.24/6.48            ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) @ ( k2_tarski @ D @ E ) ) =
% 6.24/6.48          ( k2_enumset1 @
% 6.24/6.48            ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ B @ C @ D ) @ 
% 6.24/6.48            ( k3_mcart_1 @ A @ C @ E ) @ ( k3_mcart_1 @ B @ C @ E ) ) ) )),
% 6.24/6.48    inference('cnf.neg', [status(esa)], [t44_mcart_1])).
% 6.24/6.48  thf('0', plain,
% 6.24/6.48      (((k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C) @ 
% 6.24/6.48         (k2_tarski @ sk_D @ sk_E))
% 6.24/6.48         != (k2_enumset1 @ (k3_mcart_1 @ sk_A @ sk_C @ sk_D) @ 
% 6.24/6.48             (k3_mcart_1 @ sk_B @ sk_C @ sk_D) @ 
% 6.24/6.48             (k3_mcart_1 @ sk_A @ sk_C @ sk_E) @ 
% 6.24/6.48             (k3_mcart_1 @ sk_B @ sk_C @ sk_E)))),
% 6.24/6.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.24/6.48  thf(commutativity_k2_tarski, axiom,
% 6.24/6.48    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 6.24/6.48  thf('1', plain,
% 6.24/6.48      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 6.24/6.48      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 6.24/6.48  thf(t43_enumset1, axiom,
% 6.24/6.48    (![A:$i,B:$i,C:$i]:
% 6.24/6.48     ( ( k1_enumset1 @ A @ B @ C ) =
% 6.24/6.48       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ))).
% 6.24/6.48  thf('2', plain,
% 6.24/6.48      (![X2 : $i, X3 : $i, X4 : $i]:
% 6.24/6.48         ((k1_enumset1 @ X2 @ X3 @ X4)
% 6.24/6.48           = (k2_xboole_0 @ (k2_tarski @ X2 @ X3) @ (k1_tarski @ X4)))),
% 6.24/6.48      inference('cnf', [status(esa)], [t43_enumset1])).
% 6.24/6.48  thf('3', plain,
% 6.24/6.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.24/6.48         ((k1_enumset1 @ X0 @ X1 @ X2)
% 6.24/6.48           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 6.24/6.48      inference('sup+', [status(thm)], ['1', '2'])).
% 6.24/6.48  thf('4', plain,
% 6.24/6.48      (![X2 : $i, X3 : $i, X4 : $i]:
% 6.24/6.48         ((k1_enumset1 @ X2 @ X3 @ X4)
% 6.24/6.48           = (k2_xboole_0 @ (k2_tarski @ X2 @ X3) @ (k1_tarski @ X4)))),
% 6.24/6.48      inference('cnf', [status(esa)], [t43_enumset1])).
% 6.24/6.48  thf('5', plain,
% 6.24/6.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.24/6.48         ((k1_enumset1 @ X1 @ X2 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 6.24/6.48      inference('sup+', [status(thm)], ['3', '4'])).
% 6.24/6.48  thf(t44_enumset1, axiom,
% 6.24/6.48    (![A:$i,B:$i,C:$i,D:$i]:
% 6.24/6.48     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 6.24/6.48       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 6.24/6.48  thf('6', plain,
% 6.24/6.48      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 6.24/6.48         ((k2_enumset1 @ X5 @ X6 @ X7 @ X8)
% 6.24/6.48           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k1_enumset1 @ X6 @ X7 @ X8)))),
% 6.24/6.48      inference('cnf', [status(esa)], [t44_enumset1])).
% 6.24/6.48  thf('7', plain,
% 6.24/6.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.24/6.48         ((k2_enumset1 @ X3 @ X1 @ X2 @ X0)
% 6.24/6.48           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 6.24/6.48      inference('sup+', [status(thm)], ['5', '6'])).
% 6.24/6.48  thf('8', plain,
% 6.24/6.48      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 6.24/6.48         ((k2_enumset1 @ X5 @ X6 @ X7 @ X8)
% 6.24/6.48           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k1_enumset1 @ X6 @ X7 @ X8)))),
% 6.24/6.48      inference('cnf', [status(esa)], [t44_enumset1])).
% 6.24/6.48  thf('9', plain,
% 6.24/6.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.24/6.48         ((k2_enumset1 @ X3 @ X1 @ X2 @ X0) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 6.24/6.48      inference('sup+', [status(thm)], ['7', '8'])).
% 6.24/6.48  thf('10', plain,
% 6.24/6.48      (((k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C) @ 
% 6.24/6.48         (k2_tarski @ sk_D @ sk_E))
% 6.24/6.48         != (k2_enumset1 @ (k3_mcart_1 @ sk_A @ sk_C @ sk_D) @ 
% 6.24/6.48             (k3_mcart_1 @ sk_A @ sk_C @ sk_E) @ 
% 6.24/6.48             (k3_mcart_1 @ sk_B @ sk_C @ sk_D) @ 
% 6.24/6.48             (k3_mcart_1 @ sk_B @ sk_C @ sk_E)))),
% 6.24/6.48      inference('demod', [status(thm)], ['0', '9'])).
% 6.24/6.48  thf(d3_mcart_1, axiom,
% 6.24/6.48    (![A:$i,B:$i,C:$i]:
% 6.24/6.48     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 6.24/6.48  thf('11', plain,
% 6.24/6.48      (![X22 : $i, X23 : $i, X24 : $i]:
% 6.24/6.48         ((k3_mcart_1 @ X22 @ X23 @ X24)
% 6.24/6.48           = (k4_tarski @ (k4_tarski @ X22 @ X23) @ X24))),
% 6.24/6.48      inference('cnf', [status(esa)], [d3_mcart_1])).
% 6.24/6.48  thf('12', plain,
% 6.24/6.48      (![X22 : $i, X23 : $i, X24 : $i]:
% 6.24/6.48         ((k3_mcart_1 @ X22 @ X23 @ X24)
% 6.24/6.48           = (k4_tarski @ (k4_tarski @ X22 @ X23) @ X24))),
% 6.24/6.48      inference('cnf', [status(esa)], [d3_mcart_1])).
% 6.24/6.48  thf(t146_zfmisc_1, axiom,
% 6.24/6.48    (![A:$i,B:$i,C:$i,D:$i]:
% 6.24/6.48     ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) =
% 6.24/6.48       ( k2_enumset1 @
% 6.24/6.48         ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ 
% 6.24/6.48         ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ))).
% 6.24/6.48  thf('13', plain,
% 6.24/6.48      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 6.24/6.48         ((k2_zfmisc_1 @ (k2_tarski @ X14 @ X17) @ (k2_tarski @ X15 @ X16))
% 6.24/6.48           = (k2_enumset1 @ (k4_tarski @ X14 @ X15) @ 
% 6.24/6.48              (k4_tarski @ X14 @ X16) @ (k4_tarski @ X17 @ X15) @ 
% 6.24/6.48              (k4_tarski @ X17 @ X16)))),
% 6.24/6.48      inference('cnf', [status(esa)], [t146_zfmisc_1])).
% 6.24/6.48  thf('14', plain,
% 6.24/6.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 6.24/6.48         ((k2_zfmisc_1 @ (k2_tarski @ (k4_tarski @ X2 @ X1) @ X4) @ 
% 6.24/6.48           (k2_tarski @ X0 @ X3))
% 6.24/6.48           = (k2_enumset1 @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 6.24/6.48              (k4_tarski @ (k4_tarski @ X2 @ X1) @ X3) @ 
% 6.24/6.49              (k4_tarski @ X4 @ X0) @ (k4_tarski @ X4 @ X3)))),
% 6.24/6.49      inference('sup+', [status(thm)], ['12', '13'])).
% 6.24/6.49  thf('15', plain,
% 6.24/6.49      (![X22 : $i, X23 : $i, X24 : $i]:
% 6.24/6.49         ((k3_mcart_1 @ X22 @ X23 @ X24)
% 6.24/6.49           = (k4_tarski @ (k4_tarski @ X22 @ X23) @ X24))),
% 6.24/6.49      inference('cnf', [status(esa)], [d3_mcart_1])).
% 6.24/6.49  thf('16', plain,
% 6.24/6.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 6.24/6.49         ((k2_zfmisc_1 @ (k2_tarski @ (k4_tarski @ X2 @ X1) @ X4) @ 
% 6.24/6.49           (k2_tarski @ X0 @ X3))
% 6.24/6.49           = (k2_enumset1 @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 6.24/6.49              (k3_mcart_1 @ X2 @ X1 @ X3) @ (k4_tarski @ X4 @ X0) @ 
% 6.24/6.49              (k4_tarski @ X4 @ X3)))),
% 6.24/6.49      inference('demod', [status(thm)], ['14', '15'])).
% 6.24/6.49  thf('17', plain,
% 6.24/6.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 6.24/6.49         ((k2_zfmisc_1 @ 
% 6.24/6.49           (k2_tarski @ (k4_tarski @ X5 @ X4) @ (k4_tarski @ X2 @ X1)) @ 
% 6.24/6.49           (k2_tarski @ X0 @ X3))
% 6.24/6.49           = (k2_enumset1 @ (k3_mcart_1 @ X5 @ X4 @ X0) @ 
% 6.24/6.49              (k3_mcart_1 @ X5 @ X4 @ X3) @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 6.24/6.49              (k4_tarski @ (k4_tarski @ X2 @ X1) @ X3)))),
% 6.24/6.49      inference('sup+', [status(thm)], ['11', '16'])).
% 6.24/6.49  thf('18', plain,
% 6.24/6.49      (![X22 : $i, X23 : $i, X24 : $i]:
% 6.24/6.49         ((k3_mcart_1 @ X22 @ X23 @ X24)
% 6.24/6.49           = (k4_tarski @ (k4_tarski @ X22 @ X23) @ X24))),
% 6.24/6.49      inference('cnf', [status(esa)], [d3_mcart_1])).
% 6.24/6.49  thf('19', plain,
% 6.24/6.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 6.24/6.49         ((k2_zfmisc_1 @ 
% 6.24/6.49           (k2_tarski @ (k4_tarski @ X5 @ X4) @ (k4_tarski @ X2 @ X1)) @ 
% 6.24/6.49           (k2_tarski @ X0 @ X3))
% 6.24/6.49           = (k2_enumset1 @ (k3_mcart_1 @ X5 @ X4 @ X0) @ 
% 6.24/6.49              (k3_mcart_1 @ X5 @ X4 @ X3) @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 6.24/6.49              (k3_mcart_1 @ X2 @ X1 @ X3)))),
% 6.24/6.49      inference('demod', [status(thm)], ['17', '18'])).
% 6.24/6.49  thf(t36_zfmisc_1, axiom,
% 6.24/6.49    (![A:$i,B:$i,C:$i]:
% 6.24/6.49     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 6.24/6.49         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 6.24/6.49       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 6.24/6.49         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 6.24/6.49  thf('20', plain,
% 6.24/6.49      (![X18 : $i, X19 : $i, X21 : $i]:
% 6.24/6.49         ((k2_zfmisc_1 @ (k2_tarski @ X18 @ X19) @ (k1_tarski @ X21))
% 6.24/6.49           = (k2_tarski @ (k4_tarski @ X18 @ X21) @ (k4_tarski @ X19 @ X21)))),
% 6.24/6.49      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 6.24/6.49  thf('21', plain,
% 6.24/6.49      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 6.24/6.49      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 6.24/6.49  thf('22', plain,
% 6.24/6.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.24/6.49         ((k2_tarski @ (k4_tarski @ X1 @ X0) @ (k4_tarski @ X2 @ X0))
% 6.24/6.49           = (k2_zfmisc_1 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)))),
% 6.24/6.49      inference('sup+', [status(thm)], ['20', '21'])).
% 6.24/6.49  thf('23', plain,
% 6.24/6.49      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 6.24/6.49      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 6.24/6.49  thf(d3_zfmisc_1, axiom,
% 6.24/6.49    (![A:$i,B:$i,C:$i]:
% 6.24/6.49     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 6.24/6.49       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 6.24/6.49  thf('24', plain,
% 6.24/6.49      (![X25 : $i, X26 : $i, X27 : $i]:
% 6.24/6.49         ((k3_zfmisc_1 @ X25 @ X26 @ X27)
% 6.24/6.49           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26) @ X27))),
% 6.24/6.49      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 6.24/6.49  thf('25', plain,
% 6.24/6.49      (((k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C) @ 
% 6.24/6.49         (k2_tarski @ sk_D @ sk_E))
% 6.24/6.49         != (k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C) @ 
% 6.24/6.49             (k2_tarski @ sk_D @ sk_E)))),
% 6.24/6.49      inference('demod', [status(thm)], ['10', '19', '22', '23', '24'])).
% 6.24/6.49  thf('26', plain, ($false), inference('simplify', [status(thm)], ['25'])).
% 6.24/6.49  
% 6.24/6.49  % SZS output end Refutation
% 6.24/6.49  
% 6.24/6.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
