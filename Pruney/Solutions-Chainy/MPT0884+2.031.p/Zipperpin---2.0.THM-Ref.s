%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tpqZ95xp6U

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:27 EST 2020

% Result     : Theorem 23.21s
% Output     : Refutation 23.21s
% Verified   : 
% Statistics : Number of formulae       :   41 (  57 expanded)
%              Number of leaves         :   19 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :  482 ( 715 expanded)
%              Number of equality atoms :   29 (  48 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

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

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X9 @ X10 ) @ ( k1_tarski @ X12 ) )
      = ( k2_tarski @ ( k4_tarski @ X9 @ X12 ) @ ( k4_tarski @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('2',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X9 @ X10 ) @ ( k1_tarski @ X12 ) )
      = ( k2_tarski @ ( k4_tarski @ X9 @ X12 ) @ ( k4_tarski @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X3 ) )
      = ( k2_tarski @ ( k4_tarski @ ( k4_tarski @ X2 @ X0 ) @ X3 ) @ ( k4_tarski @ ( k4_tarski @ X1 @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_zfmisc_1 @ X16 @ X17 @ X18 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_mcart_1 @ X13 @ X14 @ X15 )
      = ( k4_tarski @ ( k4_tarski @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('6',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_mcart_1 @ X13 @ X14 @ X15 )
      = ( k4_tarski @ ( k4_tarski @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k2_tarski @ ( k3_mcart_1 @ X2 @ X0 @ X3 ) @ ( k3_mcart_1 @ X1 @ X0 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('8',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_zfmisc_1 @ X16 @ X17 @ X18 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t132_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k2_tarski @ A @ B ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ B ) ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) ) ) )).

thf('9',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ ( k2_tarski @ X5 @ X7 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X8 @ ( k1_tarski @ X5 ) ) @ ( k2_zfmisc_1 @ X8 @ ( k1_tarski @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[t132_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ ( k1_tarski @ X0 ) ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k1_tarski @ X3 ) ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_zfmisc_1 @ X16 @ X17 @ X18 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('12',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_zfmisc_1 @ X16 @ X17 @ X18 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ X2 @ X1 @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ ( k1_tarski @ X0 ) ) @ ( k3_zfmisc_1 @ X2 @ X1 @ ( k1_tarski @ X3 ) ) ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_zfmisc_1 @ ( k2_tarski @ X3 @ X2 ) @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X4 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ ( k3_mcart_1 @ X3 @ X1 @ X0 ) @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) ) @ ( k3_zfmisc_1 @ ( k2_tarski @ X3 @ X2 ) @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X4 ) ) ) ) ),
    inference('sup+',[status(thm)],['7','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k2_tarski @ ( k3_mcart_1 @ X2 @ X0 @ X3 ) @ ( k3_mcart_1 @ X1 @ X0 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X5 @ X4 @ ( k3_mcart_1 @ X3 @ X1 @ X0 ) @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X5 @ X4 ) @ ( k3_zfmisc_1 @ ( k2_tarski @ X3 @ X2 ) @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_enumset1 @ ( k3_mcart_1 @ X4 @ X2 @ X1 ) @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) @ ( k3_mcart_1 @ X4 @ X2 @ X0 ) @ ( k3_mcart_1 @ X3 @ X2 @ X0 ) )
      = ( k3_zfmisc_1 @ ( k2_tarski @ X4 @ X3 ) @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    ( k3_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) )
 != ( k3_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) ) ),
    inference(demod,[status(thm)],['0','18'])).

thf('20',plain,(
    $false ),
    inference(simplify,[status(thm)],['19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tpqZ95xp6U
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:31:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 23.21/23.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 23.21/23.46  % Solved by: fo/fo7.sh
% 23.21/23.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 23.21/23.46  % done 4873 iterations in 23.047s
% 23.21/23.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 23.21/23.46  % SZS output start Refutation
% 23.21/23.46  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 23.21/23.46  thf(sk_E_type, type, sk_E: $i).
% 23.21/23.46  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 23.21/23.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 23.21/23.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 23.21/23.46  thf(sk_D_type, type, sk_D: $i).
% 23.21/23.46  thf(sk_C_type, type, sk_C: $i).
% 23.21/23.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 23.21/23.46  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 23.21/23.46  thf(sk_A_type, type, sk_A: $i).
% 23.21/23.46  thf(sk_B_type, type, sk_B: $i).
% 23.21/23.46  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 23.21/23.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 23.21/23.46  thf(t44_mcart_1, conjecture,
% 23.21/23.46    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 23.21/23.46     ( ( k3_zfmisc_1 @
% 23.21/23.46         ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) @ ( k2_tarski @ D @ E ) ) =
% 23.21/23.46       ( k2_enumset1 @
% 23.21/23.46         ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ B @ C @ D ) @ 
% 23.21/23.46         ( k3_mcart_1 @ A @ C @ E ) @ ( k3_mcart_1 @ B @ C @ E ) ) ))).
% 23.21/23.46  thf(zf_stmt_0, negated_conjecture,
% 23.21/23.46    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 23.21/23.46        ( ( k3_zfmisc_1 @
% 23.21/23.46            ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) @ ( k2_tarski @ D @ E ) ) =
% 23.21/23.46          ( k2_enumset1 @
% 23.21/23.46            ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ B @ C @ D ) @ 
% 23.21/23.46            ( k3_mcart_1 @ A @ C @ E ) @ ( k3_mcart_1 @ B @ C @ E ) ) ) )),
% 23.21/23.46    inference('cnf.neg', [status(esa)], [t44_mcart_1])).
% 23.21/23.46  thf('0', plain,
% 23.21/23.46      (((k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C) @ 
% 23.21/23.46         (k2_tarski @ sk_D @ sk_E))
% 23.21/23.46         != (k2_enumset1 @ (k3_mcart_1 @ sk_A @ sk_C @ sk_D) @ 
% 23.21/23.46             (k3_mcart_1 @ sk_B @ sk_C @ sk_D) @ 
% 23.21/23.46             (k3_mcart_1 @ sk_A @ sk_C @ sk_E) @ 
% 23.21/23.46             (k3_mcart_1 @ sk_B @ sk_C @ sk_E)))),
% 23.21/23.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.21/23.46  thf(t36_zfmisc_1, axiom,
% 23.21/23.46    (![A:$i,B:$i,C:$i]:
% 23.21/23.46     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 23.21/23.46         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 23.21/23.46       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 23.21/23.46         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 23.21/23.46  thf('1', plain,
% 23.21/23.46      (![X9 : $i, X10 : $i, X12 : $i]:
% 23.21/23.46         ((k2_zfmisc_1 @ (k2_tarski @ X9 @ X10) @ (k1_tarski @ X12))
% 23.21/23.46           = (k2_tarski @ (k4_tarski @ X9 @ X12) @ (k4_tarski @ X10 @ X12)))),
% 23.21/23.46      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 23.21/23.46  thf('2', plain,
% 23.21/23.46      (![X9 : $i, X10 : $i, X12 : $i]:
% 23.21/23.46         ((k2_zfmisc_1 @ (k2_tarski @ X9 @ X10) @ (k1_tarski @ X12))
% 23.21/23.46           = (k2_tarski @ (k4_tarski @ X9 @ X12) @ (k4_tarski @ X10 @ X12)))),
% 23.21/23.46      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 23.21/23.46  thf('3', plain,
% 23.21/23.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 23.21/23.46         ((k2_zfmisc_1 @ 
% 23.21/23.46           (k2_zfmisc_1 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)) @ 
% 23.21/23.46           (k1_tarski @ X3))
% 23.21/23.46           = (k2_tarski @ (k4_tarski @ (k4_tarski @ X2 @ X0) @ X3) @ 
% 23.21/23.46              (k4_tarski @ (k4_tarski @ X1 @ X0) @ X3)))),
% 23.21/23.46      inference('sup+', [status(thm)], ['1', '2'])).
% 23.21/23.46  thf(d3_zfmisc_1, axiom,
% 23.21/23.46    (![A:$i,B:$i,C:$i]:
% 23.21/23.46     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 23.21/23.46       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 23.21/23.46  thf('4', plain,
% 23.21/23.46      (![X16 : $i, X17 : $i, X18 : $i]:
% 23.21/23.46         ((k3_zfmisc_1 @ X16 @ X17 @ X18)
% 23.21/23.46           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17) @ X18))),
% 23.21/23.46      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 23.21/23.46  thf(d3_mcart_1, axiom,
% 23.21/23.46    (![A:$i,B:$i,C:$i]:
% 23.21/23.46     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 23.21/23.46  thf('5', plain,
% 23.21/23.46      (![X13 : $i, X14 : $i, X15 : $i]:
% 23.21/23.46         ((k3_mcart_1 @ X13 @ X14 @ X15)
% 23.21/23.46           = (k4_tarski @ (k4_tarski @ X13 @ X14) @ X15))),
% 23.21/23.46      inference('cnf', [status(esa)], [d3_mcart_1])).
% 23.21/23.46  thf('6', plain,
% 23.21/23.46      (![X13 : $i, X14 : $i, X15 : $i]:
% 23.21/23.46         ((k3_mcart_1 @ X13 @ X14 @ X15)
% 23.21/23.46           = (k4_tarski @ (k4_tarski @ X13 @ X14) @ X15))),
% 23.21/23.46      inference('cnf', [status(esa)], [d3_mcart_1])).
% 23.21/23.46  thf('7', plain,
% 23.21/23.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 23.21/23.46         ((k3_zfmisc_1 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0) @ 
% 23.21/23.46           (k1_tarski @ X3))
% 23.21/23.46           = (k2_tarski @ (k3_mcart_1 @ X2 @ X0 @ X3) @ 
% 23.21/23.46              (k3_mcart_1 @ X1 @ X0 @ X3)))),
% 23.21/23.46      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 23.21/23.46  thf('8', plain,
% 23.21/23.46      (![X16 : $i, X17 : $i, X18 : $i]:
% 23.21/23.46         ((k3_zfmisc_1 @ X16 @ X17 @ X18)
% 23.21/23.46           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17) @ X18))),
% 23.21/23.46      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 23.21/23.46  thf(t132_zfmisc_1, axiom,
% 23.21/23.46    (![A:$i,B:$i,C:$i]:
% 23.21/23.46     ( ( ( k2_zfmisc_1 @ C @ ( k2_tarski @ A @ B ) ) =
% 23.21/23.46         ( k2_xboole_0 @
% 23.21/23.46           ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ 
% 23.21/23.46           ( k2_zfmisc_1 @ C @ ( k1_tarski @ B ) ) ) ) & 
% 23.21/23.46       ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ C ) =
% 23.21/23.46         ( k2_xboole_0 @
% 23.21/23.46           ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ 
% 23.21/23.46           ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) ) ))).
% 23.21/23.46  thf('9', plain,
% 23.21/23.46      (![X5 : $i, X7 : $i, X8 : $i]:
% 23.21/23.46         ((k2_zfmisc_1 @ X8 @ (k2_tarski @ X5 @ X7))
% 23.21/23.46           = (k2_xboole_0 @ (k2_zfmisc_1 @ X8 @ (k1_tarski @ X5)) @ 
% 23.21/23.46              (k2_zfmisc_1 @ X8 @ (k1_tarski @ X7))))),
% 23.21/23.46      inference('cnf', [status(esa)], [t132_zfmisc_1])).
% 23.21/23.46  thf('10', plain,
% 23.21/23.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 23.21/23.46         ((k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ (k2_tarski @ X0 @ X3))
% 23.21/23.46           = (k2_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ (k1_tarski @ X0)) @ 
% 23.21/23.46              (k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ (k1_tarski @ X3))))),
% 23.21/23.46      inference('sup+', [status(thm)], ['8', '9'])).
% 23.21/23.46  thf('11', plain,
% 23.21/23.46      (![X16 : $i, X17 : $i, X18 : $i]:
% 23.21/23.46         ((k3_zfmisc_1 @ X16 @ X17 @ X18)
% 23.21/23.46           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17) @ X18))),
% 23.21/23.46      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 23.21/23.46  thf('12', plain,
% 23.21/23.46      (![X16 : $i, X17 : $i, X18 : $i]:
% 23.21/23.46         ((k3_zfmisc_1 @ X16 @ X17 @ X18)
% 23.21/23.46           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17) @ X18))),
% 23.21/23.46      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 23.21/23.46  thf('13', plain,
% 23.21/23.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 23.21/23.46         ((k3_zfmisc_1 @ X2 @ X1 @ (k2_tarski @ X0 @ X3))
% 23.21/23.46           = (k2_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ (k1_tarski @ X0)) @ 
% 23.21/23.46              (k3_zfmisc_1 @ X2 @ X1 @ (k1_tarski @ X3))))),
% 23.21/23.46      inference('demod', [status(thm)], ['10', '11', '12'])).
% 23.21/23.46  thf('14', plain,
% 23.21/23.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 23.21/23.46         ((k3_zfmisc_1 @ (k2_tarski @ X3 @ X2) @ (k1_tarski @ X1) @ 
% 23.21/23.46           (k2_tarski @ X0 @ X4))
% 23.21/23.46           = (k2_xboole_0 @ 
% 23.21/23.46              (k2_tarski @ (k3_mcart_1 @ X3 @ X1 @ X0) @ 
% 23.21/23.46               (k3_mcart_1 @ X2 @ X1 @ X0)) @ 
% 23.21/23.46              (k3_zfmisc_1 @ (k2_tarski @ X3 @ X2) @ (k1_tarski @ X1) @ 
% 23.21/23.46               (k1_tarski @ X4))))),
% 23.21/23.46      inference('sup+', [status(thm)], ['7', '13'])).
% 23.21/23.46  thf('15', plain,
% 23.21/23.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 23.21/23.46         ((k3_zfmisc_1 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0) @ 
% 23.21/23.46           (k1_tarski @ X3))
% 23.21/23.46           = (k2_tarski @ (k3_mcart_1 @ X2 @ X0 @ X3) @ 
% 23.21/23.46              (k3_mcart_1 @ X1 @ X0 @ X3)))),
% 23.21/23.46      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 23.21/23.46  thf(l53_enumset1, axiom,
% 23.21/23.46    (![A:$i,B:$i,C:$i,D:$i]:
% 23.21/23.46     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 23.21/23.46       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 23.21/23.46  thf('16', plain,
% 23.21/23.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 23.21/23.46         ((k2_enumset1 @ X0 @ X1 @ X2 @ X3)
% 23.21/23.46           = (k2_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X2 @ X3)))),
% 23.21/23.46      inference('cnf', [status(esa)], [l53_enumset1])).
% 23.21/23.46  thf('17', plain,
% 23.21/23.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 23.21/23.46         ((k2_enumset1 @ X5 @ X4 @ (k3_mcart_1 @ X3 @ X1 @ X0) @ 
% 23.21/23.46           (k3_mcart_1 @ X2 @ X1 @ X0))
% 23.21/23.46           = (k2_xboole_0 @ (k2_tarski @ X5 @ X4) @ 
% 23.21/23.46              (k3_zfmisc_1 @ (k2_tarski @ X3 @ X2) @ (k1_tarski @ X1) @ 
% 23.21/23.46               (k1_tarski @ X0))))),
% 23.21/23.46      inference('sup+', [status(thm)], ['15', '16'])).
% 23.21/23.46  thf('18', plain,
% 23.21/23.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 23.21/23.46         ((k2_enumset1 @ (k3_mcart_1 @ X4 @ X2 @ X1) @ 
% 23.21/23.46           (k3_mcart_1 @ X3 @ X2 @ X1) @ (k3_mcart_1 @ X4 @ X2 @ X0) @ 
% 23.21/23.46           (k3_mcart_1 @ X3 @ X2 @ X0))
% 23.21/23.46           = (k3_zfmisc_1 @ (k2_tarski @ X4 @ X3) @ (k1_tarski @ X2) @ 
% 23.21/23.46              (k2_tarski @ X1 @ X0)))),
% 23.21/23.46      inference('sup+', [status(thm)], ['14', '17'])).
% 23.21/23.46  thf('19', plain,
% 23.21/23.46      (((k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C) @ 
% 23.21/23.46         (k2_tarski @ sk_D @ sk_E))
% 23.21/23.46         != (k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C) @ 
% 23.21/23.46             (k2_tarski @ sk_D @ sk_E)))),
% 23.21/23.46      inference('demod', [status(thm)], ['0', '18'])).
% 23.21/23.46  thf('20', plain, ($false), inference('simplify', [status(thm)], ['19'])).
% 23.21/23.46  
% 23.21/23.46  % SZS output end Refutation
% 23.21/23.46  
% 23.21/23.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
