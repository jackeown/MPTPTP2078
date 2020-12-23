%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CDlFc4c1Gf

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:27 EST 2020

% Result     : Theorem 1.75s
% Output     : Refutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   37 (  40 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :  436 ( 466 expanded)
%              Number of equality atoms :   25 (  28 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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

thf(t105_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ C @ D @ B ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_enumset1 @ X4 @ X7 @ X5 @ X6 )
      = ( k2_enumset1 @ X4 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf(t103_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ D @ C ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X3 @ X2 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t103_enumset1])).

thf('3',plain,(
    ( k3_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) )
 != ( k2_enumset1 @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_D ) @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_E ) @ ( k3_mcart_1 @ sk_B @ sk_C @ sk_D ) @ ( k3_mcart_1 @ sk_B @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('4',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( k3_mcart_1 @ X40 @ X41 @ X42 )
      = ( k4_tarski @ ( k4_tarski @ X40 @ X41 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('5',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( k3_mcart_1 @ X40 @ X41 @ X42 )
      = ( k4_tarski @ ( k4_tarski @ X40 @ X41 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(t25_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
      = ( k2_enumset1 @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ) )).

thf('6',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X46 @ X49 ) @ ( k2_tarski @ X47 @ X48 ) )
      = ( k2_enumset1 @ ( k4_tarski @ X46 @ X47 ) @ ( k4_tarski @ X46 @ X48 ) @ ( k4_tarski @ X49 @ X47 ) @ ( k4_tarski @ X49 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t25_mcart_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X2 @ X1 ) @ X4 ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k4_tarski @ ( k4_tarski @ X2 @ X1 ) @ X3 ) @ ( k4_tarski @ X4 @ X0 ) @ ( k4_tarski @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( k3_mcart_1 @ X40 @ X41 @ X42 )
      = ( k4_tarski @ ( k4_tarski @ X40 @ X41 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X2 @ X1 ) @ X4 ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k3_mcart_1 @ X2 @ X1 @ X3 ) @ ( k4_tarski @ X4 @ X0 ) @ ( k4_tarski @ X4 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X5 @ X4 ) @ ( k4_tarski @ X2 @ X1 ) ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ X5 @ X4 @ X0 ) @ ( k3_mcart_1 @ X5 @ X4 @ X3 ) @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k4_tarski @ ( k4_tarski @ X2 @ X1 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( k3_mcart_1 @ X40 @ X41 @ X42 )
      = ( k4_tarski @ ( k4_tarski @ X40 @ X41 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X5 @ X4 ) @ ( k4_tarski @ X2 @ X1 ) ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ X5 @ X4 @ X0 ) @ ( k3_mcart_1 @ X5 @ X4 @ X3 ) @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k3_mcart_1 @ X2 @ X1 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('13',plain,(
    ! [X36: $i,X37: $i,X39: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X36 @ X37 ) @ ( k1_tarski @ X39 ) )
      = ( k2_tarski @ ( k4_tarski @ X36 @ X39 ) @ ( k4_tarski @ X37 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('14',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k3_zfmisc_1 @ X43 @ X44 @ X45 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) @ X45 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('15',plain,(
    ( k3_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) )
 != ( k3_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) ) ),
    inference(demod,[status(thm)],['3','12','13','14'])).

thf('16',plain,(
    $false ),
    inference(simplify,[status(thm)],['15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CDlFc4c1Gf
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:09:18 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.75/1.95  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.75/1.95  % Solved by: fo/fo7.sh
% 1.75/1.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.75/1.95  % done 1968 iterations in 1.508s
% 1.75/1.95  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.75/1.95  % SZS output start Refutation
% 1.75/1.95  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 1.75/1.95  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 1.75/1.95  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.75/1.95  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.75/1.95  thf(sk_E_type, type, sk_E: $i).
% 1.75/1.95  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 1.75/1.95  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.75/1.95  thf(sk_D_type, type, sk_D: $i).
% 1.75/1.95  thf(sk_B_type, type, sk_B: $i).
% 1.75/1.95  thf(sk_C_type, type, sk_C: $i).
% 1.75/1.95  thf(sk_A_type, type, sk_A: $i).
% 1.75/1.95  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.75/1.95  thf(t44_mcart_1, conjecture,
% 1.75/1.95    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.75/1.95     ( ( k3_zfmisc_1 @
% 1.75/1.95         ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) @ ( k2_tarski @ D @ E ) ) =
% 1.75/1.95       ( k2_enumset1 @
% 1.75/1.95         ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ B @ C @ D ) @ 
% 1.75/1.95         ( k3_mcart_1 @ A @ C @ E ) @ ( k3_mcart_1 @ B @ C @ E ) ) ))).
% 1.75/1.95  thf(zf_stmt_0, negated_conjecture,
% 1.75/1.95    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.75/1.95        ( ( k3_zfmisc_1 @
% 1.75/1.95            ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) @ ( k2_tarski @ D @ E ) ) =
% 1.75/1.95          ( k2_enumset1 @
% 1.75/1.95            ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ B @ C @ D ) @ 
% 1.75/1.95            ( k3_mcart_1 @ A @ C @ E ) @ ( k3_mcart_1 @ B @ C @ E ) ) ) )),
% 1.75/1.95    inference('cnf.neg', [status(esa)], [t44_mcart_1])).
% 1.75/1.95  thf('0', plain,
% 1.75/1.95      (((k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C) @ 
% 1.75/1.95         (k2_tarski @ sk_D @ sk_E))
% 1.75/1.95         != (k2_enumset1 @ (k3_mcart_1 @ sk_A @ sk_C @ sk_D) @ 
% 1.75/1.95             (k3_mcart_1 @ sk_B @ sk_C @ sk_D) @ 
% 1.75/1.95             (k3_mcart_1 @ sk_A @ sk_C @ sk_E) @ 
% 1.75/1.95             (k3_mcart_1 @ sk_B @ sk_C @ sk_E)))),
% 1.75/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.95  thf(t105_enumset1, axiom,
% 1.75/1.95    (![A:$i,B:$i,C:$i,D:$i]:
% 1.75/1.95     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ D @ B ) ))).
% 1.75/1.95  thf('1', plain,
% 1.75/1.95      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 1.75/1.95         ((k2_enumset1 @ X4 @ X7 @ X5 @ X6) = (k2_enumset1 @ X4 @ X5 @ X6 @ X7))),
% 1.75/1.95      inference('cnf', [status(esa)], [t105_enumset1])).
% 1.75/1.95  thf(t103_enumset1, axiom,
% 1.75/1.95    (![A:$i,B:$i,C:$i,D:$i]:
% 1.75/1.95     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ D @ C ) ))).
% 1.75/1.95  thf('2', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.75/1.95         ((k2_enumset1 @ X0 @ X1 @ X3 @ X2) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 1.75/1.95      inference('cnf', [status(esa)], [t103_enumset1])).
% 1.75/1.95  thf('3', plain,
% 1.75/1.95      (((k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C) @ 
% 1.75/1.95         (k2_tarski @ sk_D @ sk_E))
% 1.75/1.95         != (k2_enumset1 @ (k3_mcart_1 @ sk_A @ sk_C @ sk_D) @ 
% 1.75/1.95             (k3_mcart_1 @ sk_A @ sk_C @ sk_E) @ 
% 1.75/1.95             (k3_mcart_1 @ sk_B @ sk_C @ sk_D) @ 
% 1.75/1.95             (k3_mcart_1 @ sk_B @ sk_C @ sk_E)))),
% 1.75/1.95      inference('demod', [status(thm)], ['0', '1', '2'])).
% 1.75/1.95  thf(d3_mcart_1, axiom,
% 1.75/1.95    (![A:$i,B:$i,C:$i]:
% 1.75/1.95     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 1.75/1.95  thf('4', plain,
% 1.75/1.95      (![X40 : $i, X41 : $i, X42 : $i]:
% 1.75/1.95         ((k3_mcart_1 @ X40 @ X41 @ X42)
% 1.75/1.95           = (k4_tarski @ (k4_tarski @ X40 @ X41) @ X42))),
% 1.75/1.95      inference('cnf', [status(esa)], [d3_mcart_1])).
% 1.75/1.95  thf('5', plain,
% 1.75/1.95      (![X40 : $i, X41 : $i, X42 : $i]:
% 1.75/1.95         ((k3_mcart_1 @ X40 @ X41 @ X42)
% 1.75/1.95           = (k4_tarski @ (k4_tarski @ X40 @ X41) @ X42))),
% 1.75/1.95      inference('cnf', [status(esa)], [d3_mcart_1])).
% 1.75/1.95  thf(t25_mcart_1, axiom,
% 1.75/1.95    (![A:$i,B:$i,C:$i,D:$i]:
% 1.75/1.95     ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) =
% 1.75/1.95       ( k2_enumset1 @
% 1.75/1.95         ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ 
% 1.75/1.95         ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ))).
% 1.75/1.95  thf('6', plain,
% 1.75/1.95      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 1.75/1.95         ((k2_zfmisc_1 @ (k2_tarski @ X46 @ X49) @ (k2_tarski @ X47 @ X48))
% 1.75/1.95           = (k2_enumset1 @ (k4_tarski @ X46 @ X47) @ 
% 1.75/1.95              (k4_tarski @ X46 @ X48) @ (k4_tarski @ X49 @ X47) @ 
% 1.75/1.95              (k4_tarski @ X49 @ X48)))),
% 1.75/1.95      inference('cnf', [status(esa)], [t25_mcart_1])).
% 1.75/1.95  thf('7', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.75/1.95         ((k2_zfmisc_1 @ (k2_tarski @ (k4_tarski @ X2 @ X1) @ X4) @ 
% 1.75/1.95           (k2_tarski @ X0 @ X3))
% 1.75/1.95           = (k2_enumset1 @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 1.75/1.95              (k4_tarski @ (k4_tarski @ X2 @ X1) @ X3) @ 
% 1.75/1.95              (k4_tarski @ X4 @ X0) @ (k4_tarski @ X4 @ X3)))),
% 1.75/1.95      inference('sup+', [status(thm)], ['5', '6'])).
% 1.75/1.95  thf('8', plain,
% 1.75/1.95      (![X40 : $i, X41 : $i, X42 : $i]:
% 1.75/1.95         ((k3_mcart_1 @ X40 @ X41 @ X42)
% 1.75/1.95           = (k4_tarski @ (k4_tarski @ X40 @ X41) @ X42))),
% 1.75/1.95      inference('cnf', [status(esa)], [d3_mcart_1])).
% 1.75/1.95  thf('9', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.75/1.95         ((k2_zfmisc_1 @ (k2_tarski @ (k4_tarski @ X2 @ X1) @ X4) @ 
% 1.75/1.95           (k2_tarski @ X0 @ X3))
% 1.75/1.95           = (k2_enumset1 @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 1.75/1.95              (k3_mcart_1 @ X2 @ X1 @ X3) @ (k4_tarski @ X4 @ X0) @ 
% 1.75/1.95              (k4_tarski @ X4 @ X3)))),
% 1.75/1.95      inference('demod', [status(thm)], ['7', '8'])).
% 1.75/1.95  thf('10', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.75/1.95         ((k2_zfmisc_1 @ 
% 1.75/1.95           (k2_tarski @ (k4_tarski @ X5 @ X4) @ (k4_tarski @ X2 @ X1)) @ 
% 1.75/1.95           (k2_tarski @ X0 @ X3))
% 1.75/1.95           = (k2_enumset1 @ (k3_mcart_1 @ X5 @ X4 @ X0) @ 
% 1.75/1.95              (k3_mcart_1 @ X5 @ X4 @ X3) @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 1.75/1.95              (k4_tarski @ (k4_tarski @ X2 @ X1) @ X3)))),
% 1.75/1.95      inference('sup+', [status(thm)], ['4', '9'])).
% 1.75/1.95  thf('11', plain,
% 1.75/1.95      (![X40 : $i, X41 : $i, X42 : $i]:
% 1.75/1.95         ((k3_mcart_1 @ X40 @ X41 @ X42)
% 1.75/1.95           = (k4_tarski @ (k4_tarski @ X40 @ X41) @ X42))),
% 1.75/1.95      inference('cnf', [status(esa)], [d3_mcart_1])).
% 1.75/1.95  thf('12', plain,
% 1.75/1.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.75/1.95         ((k2_zfmisc_1 @ 
% 1.75/1.95           (k2_tarski @ (k4_tarski @ X5 @ X4) @ (k4_tarski @ X2 @ X1)) @ 
% 1.75/1.95           (k2_tarski @ X0 @ X3))
% 1.75/1.95           = (k2_enumset1 @ (k3_mcart_1 @ X5 @ X4 @ X0) @ 
% 1.75/1.95              (k3_mcart_1 @ X5 @ X4 @ X3) @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 1.75/1.95              (k3_mcart_1 @ X2 @ X1 @ X3)))),
% 1.75/1.95      inference('demod', [status(thm)], ['10', '11'])).
% 1.75/1.95  thf(t36_zfmisc_1, axiom,
% 1.75/1.95    (![A:$i,B:$i,C:$i]:
% 1.75/1.95     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 1.75/1.95         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 1.75/1.95       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 1.75/1.95         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 1.75/1.95  thf('13', plain,
% 1.75/1.95      (![X36 : $i, X37 : $i, X39 : $i]:
% 1.75/1.95         ((k2_zfmisc_1 @ (k2_tarski @ X36 @ X37) @ (k1_tarski @ X39))
% 1.75/1.95           = (k2_tarski @ (k4_tarski @ X36 @ X39) @ (k4_tarski @ X37 @ X39)))),
% 1.75/1.95      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 1.75/1.95  thf(d3_zfmisc_1, axiom,
% 1.75/1.95    (![A:$i,B:$i,C:$i]:
% 1.75/1.95     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 1.75/1.95       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 1.75/1.95  thf('14', plain,
% 1.75/1.95      (![X43 : $i, X44 : $i, X45 : $i]:
% 1.75/1.95         ((k3_zfmisc_1 @ X43 @ X44 @ X45)
% 1.75/1.95           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44) @ X45))),
% 1.75/1.95      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.75/1.95  thf('15', plain,
% 1.75/1.95      (((k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C) @ 
% 1.75/1.95         (k2_tarski @ sk_D @ sk_E))
% 1.75/1.95         != (k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C) @ 
% 1.75/1.95             (k2_tarski @ sk_D @ sk_E)))),
% 1.75/1.95      inference('demod', [status(thm)], ['3', '12', '13', '14'])).
% 1.75/1.95  thf('16', plain, ($false), inference('simplify', [status(thm)], ['15'])).
% 1.75/1.95  
% 1.75/1.95  % SZS output end Refutation
% 1.75/1.95  
% 1.75/1.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
