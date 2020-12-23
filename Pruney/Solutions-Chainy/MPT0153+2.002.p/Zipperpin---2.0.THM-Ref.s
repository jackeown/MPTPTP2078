%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bLW5wvqWSP

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:21 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 321 expanded)
%              Number of leaves         :   22 ( 108 expanded)
%              Depth                    :   17
%              Number of atoms          :  488 (2515 expanded)
%              Number of equality atoms :   47 ( 150 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t69_enumset1,conjecture,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k2_tarski @ A @ A )
        = ( k1_tarski @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t69_enumset1])).

thf('0',plain,(
    ( k2_tarski @ sk_A @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X15: $i,X17: $i] :
      ( ( r1_xboole_0 @ X15 @ X17 )
      | ( ( k4_xboole_0 @ X15 @ X17 )
       != X15 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != X0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['10'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('13',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('14',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['7','22'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('24',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_tarski @ X22 @ X23 )
      = ( k2_xboole_0 @ ( k1_tarski @ X22 ) @ ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('30',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('31',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('32',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','35'])).

thf('37',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['28','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t54_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('44',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X13 @ X14 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ ( k4_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t54_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['7','22'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['28','40'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['42','53'])).

thf('55',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','54'])).

thf('56',plain,(
    $false ),
    inference(simplify,[status(thm)],['55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bLW5wvqWSP
% 0.14/0.38  % Computer   : n024.cluster.edu
% 0.14/0.38  % Model      : x86_64 x86_64
% 0.14/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.38  % Memory     : 8042.1875MB
% 0.14/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.38  % CPULimit   : 60
% 0.14/0.38  % DateTime   : Tue Dec  1 13:07:51 EST 2020
% 0.14/0.38  % CPUTime    : 
% 0.14/0.38  % Running portfolio for 600 s
% 0.14/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.39  % Number of cores: 8
% 0.14/0.39  % Python version: Python 3.6.8
% 0.14/0.39  % Running in FO mode
% 0.25/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.56  % Solved by: fo/fo7.sh
% 0.25/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.56  % done 128 iterations in 0.057s
% 0.25/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.56  % SZS output start Refutation
% 0.25/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.25/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.25/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.25/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.25/0.56  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.25/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.25/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.25/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.25/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.25/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.25/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.25/0.56  thf(t69_enumset1, conjecture,
% 0.25/0.56    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.25/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.56    (~( ![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ) )),
% 0.25/0.56    inference('cnf.neg', [status(esa)], [t69_enumset1])).
% 0.25/0.56  thf('0', plain, (((k2_tarski @ sk_A @ sk_A) != (k1_tarski @ sk_A))),
% 0.25/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.56  thf(idempotence_k3_xboole_0, axiom,
% 0.25/0.56    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.25/0.56  thf('1', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.25/0.56      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.25/0.56  thf(t17_xboole_1, axiom,
% 0.25/0.56    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.25/0.56  thf('2', plain,
% 0.25/0.56      (![X10 : $i, X11 : $i]: (r1_tarski @ (k3_xboole_0 @ X10 @ X11) @ X10)),
% 0.25/0.56      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.25/0.56  thf('3', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.25/0.56      inference('sup+', [status(thm)], ['1', '2'])).
% 0.25/0.56  thf(l32_xboole_1, axiom,
% 0.25/0.56    (![A:$i,B:$i]:
% 0.25/0.56     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.25/0.56  thf('4', plain,
% 0.25/0.56      (![X7 : $i, X9 : $i]:
% 0.25/0.56         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.25/0.56      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.25/0.56  thf('5', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.25/0.56      inference('sup-', [status(thm)], ['3', '4'])).
% 0.25/0.56  thf(t98_xboole_1, axiom,
% 0.25/0.56    (![A:$i,B:$i]:
% 0.25/0.56     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.25/0.56  thf('6', plain,
% 0.25/0.56      (![X20 : $i, X21 : $i]:
% 0.25/0.56         ((k2_xboole_0 @ X20 @ X21)
% 0.25/0.56           = (k5_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20)))),
% 0.25/0.56      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.25/0.56  thf('7', plain,
% 0.25/0.56      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.25/0.56      inference('sup+', [status(thm)], ['5', '6'])).
% 0.25/0.56  thf('8', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.25/0.56      inference('sup-', [status(thm)], ['3', '4'])).
% 0.25/0.56  thf(t83_xboole_1, axiom,
% 0.25/0.56    (![A:$i,B:$i]:
% 0.25/0.56     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.25/0.56  thf('9', plain,
% 0.25/0.56      (![X15 : $i, X17 : $i]:
% 0.25/0.56         ((r1_xboole_0 @ X15 @ X17) | ((k4_xboole_0 @ X15 @ X17) != (X15)))),
% 0.25/0.56      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.25/0.56  thf('10', plain,
% 0.25/0.56      (![X0 : $i]: (((k1_xboole_0) != (X0)) | (r1_xboole_0 @ X0 @ X0))),
% 0.25/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.25/0.56  thf('11', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.25/0.56      inference('simplify', [status(thm)], ['10'])).
% 0.25/0.56  thf(t3_xboole_0, axiom,
% 0.25/0.56    (![A:$i,B:$i]:
% 0.25/0.56     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.25/0.56            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.25/0.56       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.25/0.56            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.25/0.56  thf('12', plain,
% 0.25/0.56      (![X3 : $i, X4 : $i]:
% 0.25/0.56         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.25/0.56      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.25/0.56  thf('13', plain,
% 0.25/0.56      (![X3 : $i, X4 : $i]:
% 0.25/0.56         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.25/0.56      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.25/0.56  thf('14', plain,
% 0.25/0.56      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.25/0.56         (~ (r2_hidden @ X5 @ X3)
% 0.25/0.56          | ~ (r2_hidden @ X5 @ X6)
% 0.25/0.56          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.25/0.56      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.25/0.56  thf('15', plain,
% 0.25/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.56         ((r1_xboole_0 @ X0 @ X1)
% 0.25/0.56          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.25/0.56          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.25/0.56      inference('sup-', [status(thm)], ['13', '14'])).
% 0.25/0.56  thf('16', plain,
% 0.25/0.56      (![X0 : $i, X1 : $i]:
% 0.25/0.56         ((r1_xboole_0 @ X0 @ X1)
% 0.25/0.56          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.25/0.56          | (r1_xboole_0 @ X0 @ X1))),
% 0.25/0.56      inference('sup-', [status(thm)], ['12', '15'])).
% 0.25/0.56  thf('17', plain,
% 0.25/0.56      (![X0 : $i, X1 : $i]:
% 0.25/0.56         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.25/0.56      inference('simplify', [status(thm)], ['16'])).
% 0.25/0.56  thf('18', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.25/0.56      inference('sup-', [status(thm)], ['11', '17'])).
% 0.25/0.56  thf('19', plain,
% 0.25/0.56      (![X15 : $i, X16 : $i]:
% 0.25/0.56         (((k4_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_xboole_0 @ X15 @ X16))),
% 0.25/0.56      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.25/0.56  thf('20', plain,
% 0.25/0.56      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.25/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.25/0.56  thf('21', plain,
% 0.25/0.56      (![X20 : $i, X21 : $i]:
% 0.25/0.56         ((k2_xboole_0 @ X20 @ X21)
% 0.25/0.56           = (k5_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20)))),
% 0.25/0.56      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.25/0.56  thf('22', plain,
% 0.25/0.56      (![X0 : $i]:
% 0.25/0.56         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.25/0.56      inference('sup+', [status(thm)], ['20', '21'])).
% 0.25/0.56  thf('23', plain,
% 0.25/0.56      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.25/0.56      inference('demod', [status(thm)], ['7', '22'])).
% 0.25/0.56  thf(t41_enumset1, axiom,
% 0.25/0.56    (![A:$i,B:$i]:
% 0.25/0.56     ( ( k2_tarski @ A @ B ) =
% 0.25/0.56       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.25/0.56  thf('24', plain,
% 0.25/0.56      (![X22 : $i, X23 : $i]:
% 0.25/0.56         ((k2_tarski @ X22 @ X23)
% 0.25/0.56           = (k2_xboole_0 @ (k1_tarski @ X22) @ (k1_tarski @ X23)))),
% 0.25/0.56      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.25/0.56  thf('25', plain,
% 0.25/0.56      (![X0 : $i]:
% 0.25/0.56         ((k2_tarski @ X0 @ X0)
% 0.25/0.56           = (k2_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))),
% 0.25/0.56      inference('sup+', [status(thm)], ['23', '24'])).
% 0.25/0.56  thf('26', plain,
% 0.25/0.56      (![X0 : $i]:
% 0.25/0.56         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.25/0.56      inference('sup+', [status(thm)], ['20', '21'])).
% 0.25/0.56  thf(commutativity_k5_xboole_0, axiom,
% 0.25/0.56    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.25/0.56  thf('27', plain,
% 0.25/0.56      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.25/0.56      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.25/0.56  thf('28', plain,
% 0.25/0.56      (![X0 : $i]:
% 0.25/0.56         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.25/0.56      inference('sup+', [status(thm)], ['26', '27'])).
% 0.25/0.56  thf('29', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.25/0.56      inference('sup-', [status(thm)], ['11', '17'])).
% 0.25/0.56  thf('30', plain,
% 0.25/0.56      (![X3 : $i, X4 : $i]:
% 0.25/0.56         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.25/0.56      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.25/0.56  thf('31', plain,
% 0.25/0.56      (![X3 : $i, X4 : $i]:
% 0.25/0.56         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 0.25/0.56      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.25/0.56  thf('32', plain,
% 0.25/0.56      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.25/0.56         (~ (r2_hidden @ X5 @ X3)
% 0.25/0.56          | ~ (r2_hidden @ X5 @ X6)
% 0.25/0.56          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.25/0.56      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.25/0.56  thf('33', plain,
% 0.25/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.56         ((r1_xboole_0 @ X1 @ X0)
% 0.25/0.56          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.25/0.56          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.25/0.56      inference('sup-', [status(thm)], ['31', '32'])).
% 0.25/0.56  thf('34', plain,
% 0.25/0.56      (![X0 : $i, X1 : $i]:
% 0.25/0.56         ((r1_xboole_0 @ X0 @ X1)
% 0.25/0.56          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.25/0.56          | (r1_xboole_0 @ X0 @ X1))),
% 0.25/0.56      inference('sup-', [status(thm)], ['30', '33'])).
% 0.25/0.56  thf('35', plain,
% 0.25/0.56      (![X0 : $i, X1 : $i]:
% 0.25/0.56         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.25/0.56      inference('simplify', [status(thm)], ['34'])).
% 0.25/0.56  thf('36', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.25/0.56      inference('sup-', [status(thm)], ['29', '35'])).
% 0.25/0.56  thf('37', plain,
% 0.25/0.56      (![X15 : $i, X16 : $i]:
% 0.25/0.56         (((k4_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_xboole_0 @ X15 @ X16))),
% 0.25/0.56      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.25/0.56  thf('38', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.25/0.56      inference('sup-', [status(thm)], ['36', '37'])).
% 0.25/0.56  thf('39', plain,
% 0.25/0.56      (![X20 : $i, X21 : $i]:
% 0.25/0.56         ((k2_xboole_0 @ X20 @ X21)
% 0.25/0.56           = (k5_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20)))),
% 0.25/0.56      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.25/0.56  thf('40', plain,
% 0.25/0.56      (![X0 : $i]:
% 0.25/0.56         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.25/0.56      inference('sup+', [status(thm)], ['38', '39'])).
% 0.25/0.56  thf('41', plain,
% 0.25/0.56      (![X0 : $i]:
% 0.25/0.56         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.25/0.56      inference('sup+', [status(thm)], ['28', '40'])).
% 0.25/0.56  thf('42', plain,
% 0.25/0.56      (![X0 : $i]:
% 0.25/0.56         ((k2_tarski @ X0 @ X0)
% 0.25/0.56           = (k2_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)))),
% 0.25/0.56      inference('demod', [status(thm)], ['25', '41'])).
% 0.25/0.56  thf('43', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.25/0.56      inference('sup-', [status(thm)], ['36', '37'])).
% 0.25/0.56  thf(t54_xboole_1, axiom,
% 0.25/0.56    (![A:$i,B:$i,C:$i]:
% 0.25/0.56     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 0.25/0.56       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.25/0.56  thf('44', plain,
% 0.25/0.56      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.25/0.56         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X13 @ X14))
% 0.25/0.56           = (k2_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ 
% 0.25/0.56              (k4_xboole_0 @ X12 @ X14)))),
% 0.25/0.56      inference('cnf', [status(esa)], [t54_xboole_1])).
% 0.25/0.56  thf('45', plain,
% 0.25/0.56      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.25/0.56      inference('demod', [status(thm)], ['7', '22'])).
% 0.25/0.56  thf('46', plain,
% 0.25/0.56      (![X0 : $i, X1 : $i]:
% 0.25/0.56         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X0))
% 0.25/0.56           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 0.25/0.56      inference('sup+', [status(thm)], ['44', '45'])).
% 0.25/0.56  thf('47', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.25/0.56      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.25/0.56  thf('48', plain,
% 0.25/0.56      (![X0 : $i, X1 : $i]:
% 0.25/0.56         ((k4_xboole_0 @ X1 @ X0)
% 0.25/0.56           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 0.25/0.56      inference('demod', [status(thm)], ['46', '47'])).
% 0.25/0.56  thf('49', plain,
% 0.25/0.56      (![X0 : $i]:
% 0.25/0.56         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.25/0.56      inference('sup+', [status(thm)], ['28', '40'])).
% 0.25/0.56  thf('50', plain,
% 0.25/0.56      (![X0 : $i, X1 : $i]:
% 0.25/0.56         ((k4_xboole_0 @ X1 @ X0)
% 0.25/0.56           = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.25/0.56      inference('demod', [status(thm)], ['48', '49'])).
% 0.25/0.56  thf('51', plain,
% 0.25/0.56      (![X0 : $i]:
% 0.25/0.56         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.25/0.56      inference('sup+', [status(thm)], ['43', '50'])).
% 0.25/0.56  thf('52', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.25/0.56      inference('sup-', [status(thm)], ['36', '37'])).
% 0.25/0.56  thf('53', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.25/0.56      inference('sup+', [status(thm)], ['51', '52'])).
% 0.25/0.56  thf('54', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.25/0.56      inference('demod', [status(thm)], ['42', '53'])).
% 0.25/0.56  thf('55', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 0.25/0.56      inference('demod', [status(thm)], ['0', '54'])).
% 0.25/0.56  thf('56', plain, ($false), inference('simplify', [status(thm)], ['55'])).
% 0.25/0.56  
% 0.25/0.56  % SZS output end Refutation
% 0.25/0.56  
% 0.25/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
