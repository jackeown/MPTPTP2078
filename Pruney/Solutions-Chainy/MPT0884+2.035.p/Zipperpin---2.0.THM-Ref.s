%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mZF7fk4qTt

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:27 EST 2020

% Result     : Theorem 6.36s
% Output     : Refutation 6.36s
% Verified   : 
% Statistics : Number of formulae       :   35 (  38 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :  414 ( 444 expanded)
%              Number of equality atoms :   23 (  26 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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

thf(t104_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ C @ B @ D ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X3 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t104_enumset1])).

thf('2',plain,(
    ( k3_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) )
 != ( k2_enumset1 @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_D ) @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_E ) @ ( k3_mcart_1 @ sk_B @ sk_C @ sk_D ) @ ( k3_mcart_1 @ sk_B @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('3',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( k3_mcart_1 @ X40 @ X41 @ X42 )
      = ( k4_tarski @ ( k4_tarski @ X40 @ X41 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('4',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( k3_mcart_1 @ X40 @ X41 @ X42 )
      = ( k4_tarski @ ( k4_tarski @ X40 @ X41 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(t146_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
      = ( k2_enumset1 @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ) )).

thf('5',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X32 @ X35 ) @ ( k2_tarski @ X33 @ X34 ) )
      = ( k2_enumset1 @ ( k4_tarski @ X32 @ X33 ) @ ( k4_tarski @ X32 @ X34 ) @ ( k4_tarski @ X35 @ X33 ) @ ( k4_tarski @ X35 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t146_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X2 @ X1 ) @ X4 ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k4_tarski @ ( k4_tarski @ X2 @ X1 ) @ X3 ) @ ( k4_tarski @ X4 @ X0 ) @ ( k4_tarski @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( k3_mcart_1 @ X40 @ X41 @ X42 )
      = ( k4_tarski @ ( k4_tarski @ X40 @ X41 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X2 @ X1 ) @ X4 ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k3_mcart_1 @ X2 @ X1 @ X3 ) @ ( k4_tarski @ X4 @ X0 ) @ ( k4_tarski @ X4 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X5 @ X4 ) @ ( k4_tarski @ X2 @ X1 ) ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ X5 @ X4 @ X0 ) @ ( k3_mcart_1 @ X5 @ X4 @ X3 ) @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k4_tarski @ ( k4_tarski @ X2 @ X1 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( k3_mcart_1 @ X40 @ X41 @ X42 )
      = ( k4_tarski @ ( k4_tarski @ X40 @ X41 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X5 @ X4 ) @ ( k4_tarski @ X2 @ X1 ) ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ X5 @ X4 @ X0 ) @ ( k3_mcart_1 @ X5 @ X4 @ X3 ) @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k3_mcart_1 @ X2 @ X1 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('12',plain,(
    ! [X36: $i,X37: $i,X39: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X36 @ X37 ) @ ( k1_tarski @ X39 ) )
      = ( k2_tarski @ ( k4_tarski @ X36 @ X39 ) @ ( k4_tarski @ X37 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('13',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k3_zfmisc_1 @ X43 @ X44 @ X45 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) @ X45 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('14',plain,(
    ( k3_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) )
 != ( k3_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) ) ),
    inference(demod,[status(thm)],['2','11','12','13'])).

thf('15',plain,(
    $false ),
    inference(simplify,[status(thm)],['14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mZF7fk4qTt
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:12:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 6.36/6.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.36/6.55  % Solved by: fo/fo7.sh
% 6.36/6.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.36/6.55  % done 1949 iterations in 6.096s
% 6.36/6.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.36/6.55  % SZS output start Refutation
% 6.36/6.55  thf(sk_E_type, type, sk_E: $i).
% 6.36/6.55  thf(sk_C_type, type, sk_C: $i).
% 6.36/6.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 6.36/6.55  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 6.36/6.55  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 6.36/6.55  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 6.36/6.55  thf(sk_A_type, type, sk_A: $i).
% 6.36/6.55  thf(sk_B_type, type, sk_B: $i).
% 6.36/6.55  thf(sk_D_type, type, sk_D: $i).
% 6.36/6.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 6.36/6.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 6.36/6.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.36/6.55  thf(t44_mcart_1, conjecture,
% 6.36/6.55    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 6.36/6.55     ( ( k3_zfmisc_1 @
% 6.36/6.55         ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) @ ( k2_tarski @ D @ E ) ) =
% 6.36/6.55       ( k2_enumset1 @
% 6.36/6.55         ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ B @ C @ D ) @ 
% 6.36/6.55         ( k3_mcart_1 @ A @ C @ E ) @ ( k3_mcart_1 @ B @ C @ E ) ) ))).
% 6.36/6.55  thf(zf_stmt_0, negated_conjecture,
% 6.36/6.55    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 6.36/6.55        ( ( k3_zfmisc_1 @
% 6.36/6.55            ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) @ ( k2_tarski @ D @ E ) ) =
% 6.36/6.55          ( k2_enumset1 @
% 6.36/6.55            ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ B @ C @ D ) @ 
% 6.36/6.55            ( k3_mcart_1 @ A @ C @ E ) @ ( k3_mcart_1 @ B @ C @ E ) ) ) )),
% 6.36/6.55    inference('cnf.neg', [status(esa)], [t44_mcart_1])).
% 6.36/6.55  thf('0', plain,
% 6.36/6.55      (((k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C) @ 
% 6.36/6.55         (k2_tarski @ sk_D @ sk_E))
% 6.36/6.55         != (k2_enumset1 @ (k3_mcart_1 @ sk_A @ sk_C @ sk_D) @ 
% 6.36/6.55             (k3_mcart_1 @ sk_B @ sk_C @ sk_D) @ 
% 6.36/6.55             (k3_mcart_1 @ sk_A @ sk_C @ sk_E) @ 
% 6.36/6.55             (k3_mcart_1 @ sk_B @ sk_C @ sk_E)))),
% 6.36/6.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.36/6.55  thf(t104_enumset1, axiom,
% 6.36/6.55    (![A:$i,B:$i,C:$i,D:$i]:
% 6.36/6.55     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ B @ D ) ))).
% 6.36/6.55  thf('1', plain,
% 6.36/6.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.36/6.55         ((k2_enumset1 @ X0 @ X2 @ X1 @ X3) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 6.36/6.55      inference('cnf', [status(esa)], [t104_enumset1])).
% 6.36/6.55  thf('2', plain,
% 6.36/6.55      (((k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C) @ 
% 6.36/6.55         (k2_tarski @ sk_D @ sk_E))
% 6.36/6.55         != (k2_enumset1 @ (k3_mcart_1 @ sk_A @ sk_C @ sk_D) @ 
% 6.36/6.55             (k3_mcart_1 @ sk_A @ sk_C @ sk_E) @ 
% 6.36/6.55             (k3_mcart_1 @ sk_B @ sk_C @ sk_D) @ 
% 6.36/6.55             (k3_mcart_1 @ sk_B @ sk_C @ sk_E)))),
% 6.36/6.55      inference('demod', [status(thm)], ['0', '1'])).
% 6.36/6.55  thf(d3_mcart_1, axiom,
% 6.36/6.55    (![A:$i,B:$i,C:$i]:
% 6.36/6.55     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 6.36/6.55  thf('3', plain,
% 6.36/6.55      (![X40 : $i, X41 : $i, X42 : $i]:
% 6.36/6.55         ((k3_mcart_1 @ X40 @ X41 @ X42)
% 6.36/6.55           = (k4_tarski @ (k4_tarski @ X40 @ X41) @ X42))),
% 6.36/6.55      inference('cnf', [status(esa)], [d3_mcart_1])).
% 6.36/6.55  thf('4', plain,
% 6.36/6.55      (![X40 : $i, X41 : $i, X42 : $i]:
% 6.36/6.55         ((k3_mcart_1 @ X40 @ X41 @ X42)
% 6.36/6.55           = (k4_tarski @ (k4_tarski @ X40 @ X41) @ X42))),
% 6.36/6.55      inference('cnf', [status(esa)], [d3_mcart_1])).
% 6.36/6.55  thf(t146_zfmisc_1, axiom,
% 6.36/6.55    (![A:$i,B:$i,C:$i,D:$i]:
% 6.36/6.55     ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) =
% 6.36/6.55       ( k2_enumset1 @
% 6.36/6.55         ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ 
% 6.36/6.55         ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ))).
% 6.36/6.55  thf('5', plain,
% 6.36/6.55      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 6.36/6.55         ((k2_zfmisc_1 @ (k2_tarski @ X32 @ X35) @ (k2_tarski @ X33 @ X34))
% 6.36/6.55           = (k2_enumset1 @ (k4_tarski @ X32 @ X33) @ 
% 6.36/6.55              (k4_tarski @ X32 @ X34) @ (k4_tarski @ X35 @ X33) @ 
% 6.36/6.55              (k4_tarski @ X35 @ X34)))),
% 6.36/6.55      inference('cnf', [status(esa)], [t146_zfmisc_1])).
% 6.36/6.55  thf('6', plain,
% 6.36/6.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 6.36/6.55         ((k2_zfmisc_1 @ (k2_tarski @ (k4_tarski @ X2 @ X1) @ X4) @ 
% 6.36/6.55           (k2_tarski @ X0 @ X3))
% 6.36/6.55           = (k2_enumset1 @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 6.36/6.55              (k4_tarski @ (k4_tarski @ X2 @ X1) @ X3) @ 
% 6.36/6.55              (k4_tarski @ X4 @ X0) @ (k4_tarski @ X4 @ X3)))),
% 6.36/6.55      inference('sup+', [status(thm)], ['4', '5'])).
% 6.36/6.55  thf('7', plain,
% 6.36/6.55      (![X40 : $i, X41 : $i, X42 : $i]:
% 6.36/6.55         ((k3_mcart_1 @ X40 @ X41 @ X42)
% 6.36/6.55           = (k4_tarski @ (k4_tarski @ X40 @ X41) @ X42))),
% 6.36/6.55      inference('cnf', [status(esa)], [d3_mcart_1])).
% 6.36/6.55  thf('8', plain,
% 6.36/6.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 6.36/6.55         ((k2_zfmisc_1 @ (k2_tarski @ (k4_tarski @ X2 @ X1) @ X4) @ 
% 6.36/6.55           (k2_tarski @ X0 @ X3))
% 6.36/6.55           = (k2_enumset1 @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 6.36/6.55              (k3_mcart_1 @ X2 @ X1 @ X3) @ (k4_tarski @ X4 @ X0) @ 
% 6.36/6.55              (k4_tarski @ X4 @ X3)))),
% 6.36/6.55      inference('demod', [status(thm)], ['6', '7'])).
% 6.36/6.55  thf('9', plain,
% 6.36/6.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 6.36/6.55         ((k2_zfmisc_1 @ 
% 6.36/6.55           (k2_tarski @ (k4_tarski @ X5 @ X4) @ (k4_tarski @ X2 @ X1)) @ 
% 6.36/6.55           (k2_tarski @ X0 @ X3))
% 6.36/6.55           = (k2_enumset1 @ (k3_mcart_1 @ X5 @ X4 @ X0) @ 
% 6.36/6.55              (k3_mcart_1 @ X5 @ X4 @ X3) @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 6.36/6.55              (k4_tarski @ (k4_tarski @ X2 @ X1) @ X3)))),
% 6.36/6.55      inference('sup+', [status(thm)], ['3', '8'])).
% 6.36/6.55  thf('10', plain,
% 6.36/6.55      (![X40 : $i, X41 : $i, X42 : $i]:
% 6.36/6.55         ((k3_mcart_1 @ X40 @ X41 @ X42)
% 6.36/6.55           = (k4_tarski @ (k4_tarski @ X40 @ X41) @ X42))),
% 6.36/6.55      inference('cnf', [status(esa)], [d3_mcart_1])).
% 6.36/6.55  thf('11', plain,
% 6.36/6.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 6.36/6.55         ((k2_zfmisc_1 @ 
% 6.36/6.55           (k2_tarski @ (k4_tarski @ X5 @ X4) @ (k4_tarski @ X2 @ X1)) @ 
% 6.36/6.55           (k2_tarski @ X0 @ X3))
% 6.36/6.55           = (k2_enumset1 @ (k3_mcart_1 @ X5 @ X4 @ X0) @ 
% 6.36/6.55              (k3_mcart_1 @ X5 @ X4 @ X3) @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 6.36/6.55              (k3_mcart_1 @ X2 @ X1 @ X3)))),
% 6.36/6.55      inference('demod', [status(thm)], ['9', '10'])).
% 6.36/6.55  thf(t36_zfmisc_1, axiom,
% 6.36/6.55    (![A:$i,B:$i,C:$i]:
% 6.36/6.55     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 6.36/6.55         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 6.36/6.55       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 6.36/6.55         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 6.36/6.55  thf('12', plain,
% 6.36/6.55      (![X36 : $i, X37 : $i, X39 : $i]:
% 6.36/6.55         ((k2_zfmisc_1 @ (k2_tarski @ X36 @ X37) @ (k1_tarski @ X39))
% 6.36/6.55           = (k2_tarski @ (k4_tarski @ X36 @ X39) @ (k4_tarski @ X37 @ X39)))),
% 6.36/6.55      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 6.36/6.55  thf(d3_zfmisc_1, axiom,
% 6.36/6.55    (![A:$i,B:$i,C:$i]:
% 6.36/6.55     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 6.36/6.55       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 6.36/6.55  thf('13', plain,
% 6.36/6.55      (![X43 : $i, X44 : $i, X45 : $i]:
% 6.36/6.55         ((k3_zfmisc_1 @ X43 @ X44 @ X45)
% 6.36/6.55           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44) @ X45))),
% 6.36/6.55      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 6.36/6.55  thf('14', plain,
% 6.36/6.55      (((k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C) @ 
% 6.36/6.55         (k2_tarski @ sk_D @ sk_E))
% 6.36/6.55         != (k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C) @ 
% 6.36/6.55             (k2_tarski @ sk_D @ sk_E)))),
% 6.36/6.55      inference('demod', [status(thm)], ['2', '11', '12', '13'])).
% 6.36/6.55  thf('15', plain, ($false), inference('simplify', [status(thm)], ['14'])).
% 6.36/6.55  
% 6.36/6.55  % SZS output end Refutation
% 6.36/6.55  
% 6.36/6.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
