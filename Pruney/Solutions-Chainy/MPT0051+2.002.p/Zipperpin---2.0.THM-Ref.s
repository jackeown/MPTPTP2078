%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7M1I0ESRGy

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:05 EST 2020

% Result     : Theorem 3.08s
% Output     : Refutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 111 expanded)
%              Number of leaves         :   13 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :  487 ( 835 expanded)
%              Number of equality atoms :   38 (  71 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t44_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
       => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,(
    ~ ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('4',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ X2 @ ( k2_xboole_0 @ X4 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ sk_C @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ sk_C @ X0 ) )
      = ( k2_xboole_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ sk_C @ X0 ) @ ( k4_xboole_0 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_C @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','17'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('24',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','17'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['22','25','26','27'])).

thf('29',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_B )
    = ( k2_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['11','28'])).

thf('30',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('31',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('34',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ X2 @ ( k2_xboole_0 @ X4 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['32','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','17'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['38','41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('45',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_B )
    = ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','43','44'])).

thf('46',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('47',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['2','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7M1I0ESRGy
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:59:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.08/3.29  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.08/3.29  % Solved by: fo/fo7.sh
% 3.08/3.29  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.08/3.29  % done 3101 iterations in 2.840s
% 3.08/3.29  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.08/3.29  % SZS output start Refutation
% 3.08/3.29  thf(sk_A_type, type, sk_A: $i).
% 3.08/3.29  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.08/3.29  thf(sk_C_type, type, sk_C: $i).
% 3.08/3.29  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.08/3.29  thf(sk_B_type, type, sk_B: $i).
% 3.08/3.29  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.08/3.29  thf(t44_xboole_1, conjecture,
% 3.08/3.29    (![A:$i,B:$i,C:$i]:
% 3.08/3.29     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 3.08/3.29       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 3.08/3.29  thf(zf_stmt_0, negated_conjecture,
% 3.08/3.29    (~( ![A:$i,B:$i,C:$i]:
% 3.08/3.29        ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 3.08/3.29          ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )),
% 3.08/3.29    inference('cnf.neg', [status(esa)], [t44_xboole_1])).
% 3.08/3.29  thf('0', plain, (~ (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))),
% 3.08/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.08/3.29  thf(commutativity_k2_xboole_0, axiom,
% 3.08/3.29    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 3.08/3.29  thf('1', plain,
% 3.08/3.29      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.08/3.29      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.08/3.29  thf('2', plain, (~ (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B))),
% 3.08/3.29      inference('demod', [status(thm)], ['0', '1'])).
% 3.08/3.29  thf('3', plain,
% 3.08/3.29      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.08/3.29      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.08/3.29  thf('4', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C)),
% 3.08/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.08/3.29  thf(t10_xboole_1, axiom,
% 3.08/3.29    (![A:$i,B:$i,C:$i]:
% 3.08/3.29     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 3.08/3.29  thf('5', plain,
% 3.08/3.29      (![X2 : $i, X3 : $i, X4 : $i]:
% 3.08/3.29         (~ (r1_tarski @ X2 @ X3) | (r1_tarski @ X2 @ (k2_xboole_0 @ X4 @ X3)))),
% 3.08/3.29      inference('cnf', [status(esa)], [t10_xboole_1])).
% 3.08/3.29  thf('6', plain,
% 3.08/3.29      (![X0 : $i]:
% 3.08/3.29         (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ (k2_xboole_0 @ X0 @ sk_C))),
% 3.08/3.29      inference('sup-', [status(thm)], ['4', '5'])).
% 3.08/3.29  thf('7', plain,
% 3.08/3.29      (![X0 : $i]:
% 3.08/3.29         (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ (k2_xboole_0 @ sk_C @ X0))),
% 3.08/3.29      inference('sup+', [status(thm)], ['3', '6'])).
% 3.08/3.29  thf(t12_xboole_1, axiom,
% 3.08/3.29    (![A:$i,B:$i]:
% 3.08/3.29     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 3.08/3.29  thf('8', plain,
% 3.08/3.29      (![X5 : $i, X6 : $i]:
% 3.08/3.29         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 3.08/3.29      inference('cnf', [status(esa)], [t12_xboole_1])).
% 3.08/3.29  thf('9', plain,
% 3.08/3.29      (![X0 : $i]:
% 3.08/3.29         ((k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 3.08/3.29           (k2_xboole_0 @ sk_C @ X0)) = (k2_xboole_0 @ sk_C @ X0))),
% 3.08/3.29      inference('sup-', [status(thm)], ['7', '8'])).
% 3.08/3.29  thf('10', plain,
% 3.08/3.29      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.08/3.29      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.08/3.29  thf('11', plain,
% 3.08/3.29      (![X0 : $i]:
% 3.08/3.29         ((k2_xboole_0 @ (k2_xboole_0 @ sk_C @ X0) @ 
% 3.08/3.29           (k4_xboole_0 @ sk_A @ sk_B)) = (k2_xboole_0 @ sk_C @ X0))),
% 3.08/3.29      inference('sup+', [status(thm)], ['9', '10'])).
% 3.08/3.29  thf('12', plain,
% 3.08/3.29      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.08/3.29      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.08/3.29  thf('13', plain,
% 3.08/3.29      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.08/3.29      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.08/3.29  thf(t7_xboole_1, axiom,
% 3.08/3.29    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 3.08/3.29  thf('14', plain,
% 3.08/3.29      (![X12 : $i, X13 : $i]: (r1_tarski @ X12 @ (k2_xboole_0 @ X12 @ X13))),
% 3.08/3.29      inference('cnf', [status(esa)], [t7_xboole_1])).
% 3.08/3.29  thf('15', plain,
% 3.08/3.29      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 3.08/3.29      inference('sup+', [status(thm)], ['13', '14'])).
% 3.08/3.29  thf('16', plain,
% 3.08/3.29      (![X5 : $i, X6 : $i]:
% 3.08/3.29         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 3.08/3.29      inference('cnf', [status(esa)], [t12_xboole_1])).
% 3.08/3.29  thf('17', plain,
% 3.08/3.29      (![X0 : $i, X1 : $i]:
% 3.08/3.29         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 3.08/3.29           = (k2_xboole_0 @ X1 @ X0))),
% 3.08/3.29      inference('sup-', [status(thm)], ['15', '16'])).
% 3.08/3.29  thf('18', plain,
% 3.08/3.29      (![X0 : $i, X1 : $i]:
% 3.08/3.29         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 3.08/3.29           = (k2_xboole_0 @ X0 @ X1))),
% 3.08/3.29      inference('sup+', [status(thm)], ['12', '17'])).
% 3.08/3.29  thf(t41_xboole_1, axiom,
% 3.08/3.29    (![A:$i,B:$i,C:$i]:
% 3.08/3.29     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 3.08/3.29       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 3.08/3.29  thf('19', plain,
% 3.08/3.29      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.08/3.29         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 3.08/3.29           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 3.08/3.29      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.08/3.29  thf(t39_xboole_1, axiom,
% 3.08/3.29    (![A:$i,B:$i]:
% 3.08/3.29     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 3.08/3.29  thf('20', plain,
% 3.08/3.29      (![X7 : $i, X8 : $i]:
% 3.08/3.29         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 3.08/3.29           = (k2_xboole_0 @ X7 @ X8))),
% 3.08/3.29      inference('cnf', [status(esa)], [t39_xboole_1])).
% 3.08/3.29  thf('21', plain,
% 3.08/3.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.08/3.29         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 3.08/3.29           (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 3.08/3.29           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 3.08/3.29      inference('sup+', [status(thm)], ['19', '20'])).
% 3.08/3.29  thf('22', plain,
% 3.08/3.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.08/3.29         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 3.08/3.29           (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ (k2_xboole_0 @ X0 @ X1)))
% 3.08/3.29           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) @ X2))),
% 3.08/3.29      inference('sup+', [status(thm)], ['18', '21'])).
% 3.08/3.29  thf('23', plain,
% 3.08/3.29      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.08/3.29      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.08/3.29  thf('24', plain,
% 3.08/3.29      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.08/3.29         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 3.08/3.29           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 3.08/3.29      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.08/3.29  thf('25', plain,
% 3.08/3.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.08/3.29         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 3.08/3.29           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 3.08/3.29      inference('sup+', [status(thm)], ['23', '24'])).
% 3.08/3.29  thf('26', plain,
% 3.08/3.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.08/3.29         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 3.08/3.29           (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 3.08/3.29           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 3.08/3.29      inference('sup+', [status(thm)], ['19', '20'])).
% 3.08/3.29  thf('27', plain,
% 3.08/3.29      (![X0 : $i, X1 : $i]:
% 3.08/3.29         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 3.08/3.29           = (k2_xboole_0 @ X0 @ X1))),
% 3.08/3.29      inference('sup+', [status(thm)], ['12', '17'])).
% 3.08/3.29  thf('28', plain,
% 3.08/3.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.08/3.29         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X2 @ X0))
% 3.08/3.29           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 3.08/3.29      inference('demod', [status(thm)], ['22', '25', '26', '27'])).
% 3.08/3.29  thf('29', plain,
% 3.08/3.29      (((k2_xboole_0 @ sk_C @ sk_B)
% 3.08/3.29         = (k2_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_B) @ sk_A))),
% 3.08/3.29      inference('sup+', [status(thm)], ['11', '28'])).
% 3.08/3.29  thf('30', plain,
% 3.08/3.29      (![X12 : $i, X13 : $i]: (r1_tarski @ X12 @ (k2_xboole_0 @ X12 @ X13))),
% 3.08/3.29      inference('cnf', [status(esa)], [t7_xboole_1])).
% 3.08/3.29  thf('31', plain,
% 3.08/3.29      (![X5 : $i, X6 : $i]:
% 3.08/3.29         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 3.08/3.29      inference('cnf', [status(esa)], [t12_xboole_1])).
% 3.08/3.29  thf('32', plain,
% 3.08/3.29      (![X0 : $i, X1 : $i]:
% 3.08/3.29         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 3.08/3.29           = (k2_xboole_0 @ X1 @ X0))),
% 3.08/3.29      inference('sup-', [status(thm)], ['30', '31'])).
% 3.08/3.29  thf('33', plain,
% 3.08/3.29      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 3.08/3.29      inference('sup+', [status(thm)], ['13', '14'])).
% 3.08/3.29  thf('34', plain,
% 3.08/3.29      (![X2 : $i, X3 : $i, X4 : $i]:
% 3.08/3.29         (~ (r1_tarski @ X2 @ X3) | (r1_tarski @ X2 @ (k2_xboole_0 @ X4 @ X3)))),
% 3.08/3.29      inference('cnf', [status(esa)], [t10_xboole_1])).
% 3.08/3.29  thf('35', plain,
% 3.08/3.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.08/3.29         (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 3.08/3.29      inference('sup-', [status(thm)], ['33', '34'])).
% 3.08/3.29  thf('36', plain,
% 3.08/3.29      (![X5 : $i, X6 : $i]:
% 3.08/3.29         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 3.08/3.29      inference('cnf', [status(esa)], [t12_xboole_1])).
% 3.08/3.29  thf('37', plain,
% 3.08/3.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.08/3.29         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 3.08/3.29           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 3.08/3.29      inference('sup-', [status(thm)], ['35', '36'])).
% 3.08/3.29  thf('38', plain,
% 3.08/3.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.08/3.29         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 3.08/3.29           (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 3.08/3.29           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))))),
% 3.08/3.29      inference('sup+', [status(thm)], ['32', '37'])).
% 3.08/3.29  thf('39', plain,
% 3.08/3.29      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.08/3.29      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.08/3.29  thf('40', plain,
% 3.08/3.29      (![X0 : $i, X1 : $i]:
% 3.08/3.29         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 3.08/3.29           = (k2_xboole_0 @ X1 @ X0))),
% 3.08/3.29      inference('sup-', [status(thm)], ['30', '31'])).
% 3.08/3.29  thf('41', plain,
% 3.08/3.29      (![X0 : $i, X1 : $i]:
% 3.08/3.29         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 3.08/3.29           = (k2_xboole_0 @ X0 @ X1))),
% 3.08/3.29      inference('sup+', [status(thm)], ['39', '40'])).
% 3.08/3.29  thf('42', plain,
% 3.08/3.29      (![X0 : $i, X1 : $i]:
% 3.08/3.29         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 3.08/3.29           = (k2_xboole_0 @ X0 @ X1))),
% 3.08/3.29      inference('sup+', [status(thm)], ['12', '17'])).
% 3.08/3.29  thf('43', plain,
% 3.08/3.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.08/3.29         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 3.08/3.29           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1)))),
% 3.08/3.29      inference('demod', [status(thm)], ['38', '41', '42'])).
% 3.08/3.29  thf('44', plain,
% 3.08/3.29      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.08/3.29      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.08/3.29  thf('45', plain,
% 3.08/3.29      (((k2_xboole_0 @ sk_C @ sk_B)
% 3.08/3.29         = (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B)))),
% 3.08/3.29      inference('demod', [status(thm)], ['29', '43', '44'])).
% 3.08/3.29  thf('46', plain,
% 3.08/3.29      (![X12 : $i, X13 : $i]: (r1_tarski @ X12 @ (k2_xboole_0 @ X12 @ X13))),
% 3.08/3.29      inference('cnf', [status(esa)], [t7_xboole_1])).
% 3.08/3.29  thf('47', plain, ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B))),
% 3.08/3.29      inference('sup+', [status(thm)], ['45', '46'])).
% 3.08/3.29  thf('48', plain, ($false), inference('demod', [status(thm)], ['2', '47'])).
% 3.08/3.29  
% 3.08/3.29  % SZS output end Refutation
% 3.08/3.29  
% 3.08/3.30  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
