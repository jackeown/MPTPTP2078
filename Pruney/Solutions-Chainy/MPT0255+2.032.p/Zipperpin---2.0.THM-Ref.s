%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.a3BYWcseoF

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 103 expanded)
%              Number of leaves         :   18 (  40 expanded)
%              Depth                    :   15
%              Number of atoms          :  255 ( 553 expanded)
%              Number of equality atoms :   44 (  93 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(t50_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t50_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('2',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('3',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('4',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['2','3'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X9 @ X10 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('7',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('8',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('9',plain,
    ( k1_xboole_0
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('11',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('13',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k2_tarski @ k1_xboole_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['4','13'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k2_tarski @ k1_xboole_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['4','13'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('20',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_tarski @ X5 @ X4 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ sk_B @ ( k4_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X9 @ X10 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ k1_xboole_0 )
      = ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['23','24','27'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('29',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('30',plain,
    ( ( k1_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['14','28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('32',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X11 ) @ X12 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['30','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.a3BYWcseoF
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:36:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 58 iterations in 0.013s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.50  thf(t50_zfmisc_1, conjecture,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.50        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t46_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (![X2 : $i, X3 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X2 @ X3)) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['0', '1'])).
% 0.21/0.50  thf(t3_boole, axiom,
% 0.21/0.50    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.50  thf('3', plain, (![X1 : $i]: ((k4_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.50  thf('4', plain, (((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.50  thf('5', plain, (((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.50  thf(l51_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X9 : $i, X10 : $i]:
% 0.21/0.50         ((k3_tarski @ (k2_tarski @ X9 @ X10)) = (k2_xboole_0 @ X9 @ X10))),
% 0.21/0.50      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.50  thf('7', plain, (((k3_tarski @ k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.50      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.50  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.21/0.50  thf('8', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.21/0.50  thf('9', plain, (((k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (![X2 : $i, X3 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X2 @ X3)) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.21/0.50  thf('11', plain, (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.50  thf('12', plain, (![X1 : $i]: ((k4_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.50  thf('13', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.50  thf('14', plain, (((k2_tarski @ k1_xboole_0 @ sk_B) = (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['4', '13'])).
% 0.21/0.50  thf(t1_boole, axiom,
% 0.21/0.50    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.50  thf('15', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t1_boole])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X2 : $i, X3 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X2 @ X3)) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.21/0.50  thf('17', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['15', '16'])).
% 0.21/0.50  thf('18', plain, (((k2_tarski @ k1_xboole_0 @ sk_B) = (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['4', '13'])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k2_tarski @ (k4_xboole_0 @ X0 @ X0) @ sk_B) = (k1_xboole_0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['17', '18'])).
% 0.21/0.50  thf(commutativity_k2_tarski, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X4 : $i, X5 : $i]: ((k2_tarski @ X5 @ X4) = (k2_tarski @ X4 @ X5))),
% 0.21/0.50      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k2_tarski @ sk_B @ (k4_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['19', '20'])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (![X9 : $i, X10 : $i]:
% 0.21/0.50         ((k3_tarski @ (k2_tarski @ X9 @ X10)) = (k2_xboole_0 @ X9 @ X10))),
% 0.21/0.50      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k3_tarski @ k1_xboole_0)
% 0.21/0.50           = (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ X0)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['21', '22'])).
% 0.21/0.50  thf('24', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.21/0.50  thf('25', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['15', '16'])).
% 0.21/0.50  thf('26', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t1_boole])).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 0.21/0.50      inference('sup+', [status(thm)], ['25', '26'])).
% 0.21/0.50  thf('28', plain, (((k1_xboole_0) = (sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['23', '24', '27'])).
% 0.21/0.50  thf(t69_enumset1, axiom,
% 0.21/0.50    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.50  thf('29', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.50  thf('30', plain, (((k1_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['14', '28', '29'])).
% 0.21/0.50  thf('31', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t1_boole])).
% 0.21/0.50  thf(t49_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      (![X11 : $i, X12 : $i]:
% 0.21/0.50         ((k2_xboole_0 @ (k1_tarski @ X11) @ X12) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.21/0.50  thf('33', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.50  thf('34', plain, ($false),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['30', '33'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
