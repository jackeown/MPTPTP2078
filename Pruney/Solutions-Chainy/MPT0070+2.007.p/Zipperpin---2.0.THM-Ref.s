%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YnQlPkpaAv

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:33 EST 2020

% Result     : Theorem 0.57s
% Output     : Refutation 0.57s
% Verified   : 
% Statistics : Number of formulae       :   78 (  99 expanded)
%              Number of leaves         :   19 (  38 expanded)
%              Depth                    :   20
%              Number of atoms          :  505 ( 684 expanded)
%              Number of equality atoms :   56 (  73 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t63_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_xboole_0 @ B @ C ) )
       => ( r1_xboole_0 @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t63_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('7',plain,(
    r1_xboole_0 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('11',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('14',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('19',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['9','18'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('20',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('21',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('22',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ X0 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['6','23'])).

thf('25',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('26',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ X0 ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('32',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('35',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','38'])).

thf('40',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','41','42'])).

thf('44',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C @ ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['4','47'])).

thf('49',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference('sup+',[status(thm)],['3','48'])).

thf('50',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('51',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('53',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('55',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['0','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YnQlPkpaAv
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:10:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.57/0.80  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.57/0.80  % Solved by: fo/fo7.sh
% 0.57/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.57/0.80  % done 954 iterations in 0.337s
% 0.57/0.80  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.57/0.80  % SZS output start Refutation
% 0.57/0.80  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.57/0.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.57/0.80  thf(sk_C_type, type, sk_C: $i).
% 0.57/0.80  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.57/0.80  thf(sk_B_type, type, sk_B: $i).
% 0.57/0.80  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.57/0.80  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.57/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.57/0.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.57/0.80  thf(t63_xboole_1, conjecture,
% 0.57/0.80    (![A:$i,B:$i,C:$i]:
% 0.57/0.80     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.57/0.80       ( r1_xboole_0 @ A @ C ) ))).
% 0.57/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.57/0.80    (~( ![A:$i,B:$i,C:$i]:
% 0.57/0.80        ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.57/0.80          ( r1_xboole_0 @ A @ C ) ) )),
% 0.57/0.80    inference('cnf.neg', [status(esa)], [t63_xboole_1])).
% 0.57/0.80  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_C)),
% 0.57/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.80  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.57/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.80  thf(t28_xboole_1, axiom,
% 0.57/0.80    (![A:$i,B:$i]:
% 0.57/0.80     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.57/0.80  thf('2', plain,
% 0.57/0.80      (![X8 : $i, X9 : $i]:
% 0.57/0.80         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.57/0.80      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.57/0.80  thf('3', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.57/0.80      inference('sup-', [status(thm)], ['1', '2'])).
% 0.57/0.80  thf(commutativity_k3_xboole_0, axiom,
% 0.57/0.80    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.57/0.80  thf('4', plain,
% 0.57/0.80      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.57/0.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.57/0.80  thf(t48_xboole_1, axiom,
% 0.57/0.80    (![A:$i,B:$i]:
% 0.57/0.80     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.57/0.80  thf('5', plain,
% 0.57/0.80      (![X16 : $i, X17 : $i]:
% 0.57/0.80         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.57/0.80           = (k3_xboole_0 @ X16 @ X17))),
% 0.57/0.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.57/0.80  thf(commutativity_k2_xboole_0, axiom,
% 0.57/0.80    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.57/0.80  thf('6', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.57/0.80      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.57/0.80  thf('7', plain, ((r1_xboole_0 @ sk_B @ sk_C)),
% 0.57/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.80  thf(d7_xboole_0, axiom,
% 0.57/0.80    (![A:$i,B:$i]:
% 0.57/0.80     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.57/0.80       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.57/0.80  thf('8', plain,
% 0.57/0.80      (![X4 : $i, X5 : $i]:
% 0.57/0.80         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.57/0.80      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.57/0.80  thf('9', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))),
% 0.57/0.80      inference('sup-', [status(thm)], ['7', '8'])).
% 0.57/0.80  thf('10', plain,
% 0.57/0.80      (![X16 : $i, X17 : $i]:
% 0.57/0.80         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.57/0.80           = (k3_xboole_0 @ X16 @ X17))),
% 0.57/0.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.57/0.80  thf('11', plain,
% 0.57/0.80      (![X16 : $i, X17 : $i]:
% 0.57/0.80         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.57/0.80           = (k3_xboole_0 @ X16 @ X17))),
% 0.57/0.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.57/0.80  thf('12', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i]:
% 0.57/0.80         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.57/0.80           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.57/0.80      inference('sup+', [status(thm)], ['10', '11'])).
% 0.57/0.80  thf(t36_xboole_1, axiom,
% 0.57/0.80    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.57/0.80  thf('13', plain,
% 0.57/0.80      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 0.57/0.80      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.57/0.80  thf('14', plain,
% 0.57/0.80      (![X8 : $i, X9 : $i]:
% 0.57/0.80         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.57/0.80      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.57/0.80  thf('15', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i]:
% 0.57/0.80         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.57/0.80           = (k4_xboole_0 @ X0 @ X1))),
% 0.57/0.80      inference('sup-', [status(thm)], ['13', '14'])).
% 0.57/0.80  thf('16', plain,
% 0.57/0.80      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.57/0.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.57/0.80  thf('17', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i]:
% 0.57/0.80         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.57/0.80           = (k4_xboole_0 @ X0 @ X1))),
% 0.57/0.80      inference('demod', [status(thm)], ['15', '16'])).
% 0.57/0.80  thf('18', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i]:
% 0.57/0.80         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.57/0.80           = (k4_xboole_0 @ X1 @ X0))),
% 0.57/0.80      inference('demod', [status(thm)], ['12', '17'])).
% 0.57/0.80  thf('19', plain,
% 0.57/0.80      (((k4_xboole_0 @ sk_B @ k1_xboole_0) = (k4_xboole_0 @ sk_B @ sk_C))),
% 0.57/0.80      inference('sup+', [status(thm)], ['9', '18'])).
% 0.57/0.80  thf(t3_boole, axiom,
% 0.57/0.80    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.57/0.80  thf('20', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.57/0.80      inference('cnf', [status(esa)], [t3_boole])).
% 0.57/0.80  thf('21', plain, (((sk_B) = (k4_xboole_0 @ sk_B @ sk_C))),
% 0.57/0.80      inference('demod', [status(thm)], ['19', '20'])).
% 0.57/0.80  thf(t41_xboole_1, axiom,
% 0.57/0.80    (![A:$i,B:$i,C:$i]:
% 0.57/0.80     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.57/0.80       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.57/0.80  thf('22', plain,
% 0.57/0.80      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.57/0.80         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 0.57/0.80           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 0.57/0.80      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.57/0.80  thf('23', plain,
% 0.57/0.80      (![X0 : $i]:
% 0.57/0.80         ((k4_xboole_0 @ sk_B @ X0)
% 0.57/0.80           = (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C @ X0)))),
% 0.57/0.80      inference('sup+', [status(thm)], ['21', '22'])).
% 0.57/0.80  thf('24', plain,
% 0.57/0.80      (![X0 : $i]:
% 0.57/0.80         ((k4_xboole_0 @ sk_B @ X0)
% 0.57/0.80           = (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ X0 @ sk_C)))),
% 0.57/0.80      inference('sup+', [status(thm)], ['6', '23'])).
% 0.57/0.80  thf('25', plain,
% 0.57/0.80      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.57/0.80         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 0.57/0.80           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 0.57/0.80      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.57/0.80  thf('26', plain,
% 0.57/0.80      (![X16 : $i, X17 : $i]:
% 0.57/0.80         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.57/0.80           = (k3_xboole_0 @ X16 @ X17))),
% 0.57/0.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.57/0.80  thf('27', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.80         ((k4_xboole_0 @ X2 @ 
% 0.57/0.80           (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))
% 0.57/0.80           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.57/0.80      inference('sup+', [status(thm)], ['25', '26'])).
% 0.57/0.80  thf('28', plain,
% 0.57/0.80      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.57/0.80         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 0.57/0.80           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 0.57/0.80      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.57/0.80  thf('29', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.80         ((k4_xboole_0 @ X2 @ 
% 0.57/0.80           (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))
% 0.57/0.80           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.57/0.80      inference('demod', [status(thm)], ['27', '28'])).
% 0.57/0.80  thf('30', plain,
% 0.57/0.80      (![X0 : $i]:
% 0.57/0.80         ((k4_xboole_0 @ sk_B @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ X0)))
% 0.57/0.80           = (k3_xboole_0 @ (k4_xboole_0 @ sk_B @ X0) @ sk_C))),
% 0.57/0.80      inference('sup+', [status(thm)], ['24', '29'])).
% 0.57/0.80  thf('31', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.57/0.80      inference('cnf', [status(esa)], [t3_boole])).
% 0.57/0.80  thf('32', plain,
% 0.57/0.80      (![X16 : $i, X17 : $i]:
% 0.57/0.80         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.57/0.80           = (k3_xboole_0 @ X16 @ X17))),
% 0.57/0.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.57/0.80  thf('33', plain,
% 0.57/0.80      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.57/0.80      inference('sup+', [status(thm)], ['31', '32'])).
% 0.57/0.80  thf('34', plain,
% 0.57/0.80      (![X16 : $i, X17 : $i]:
% 0.57/0.80         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.57/0.80           = (k3_xboole_0 @ X16 @ X17))),
% 0.57/0.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.57/0.80  thf(t4_boole, axiom,
% 0.57/0.80    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.57/0.80  thf('35', plain,
% 0.57/0.80      (![X18 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X18) = (k1_xboole_0))),
% 0.57/0.80      inference('cnf', [status(esa)], [t4_boole])).
% 0.57/0.80  thf('36', plain,
% 0.57/0.80      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.57/0.80      inference('sup+', [status(thm)], ['34', '35'])).
% 0.57/0.80  thf('37', plain,
% 0.57/0.80      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.57/0.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.57/0.80  thf('38', plain,
% 0.57/0.80      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.57/0.80      inference('sup+', [status(thm)], ['36', '37'])).
% 0.57/0.80  thf('39', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.57/0.80      inference('demod', [status(thm)], ['33', '38'])).
% 0.57/0.80  thf('40', plain,
% 0.57/0.80      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.57/0.80         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 0.57/0.80           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 0.57/0.80      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.57/0.80  thf('41', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i]:
% 0.57/0.80         ((k1_xboole_0)
% 0.57/0.80           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.57/0.80      inference('sup+', [status(thm)], ['39', '40'])).
% 0.57/0.80  thf('42', plain,
% 0.57/0.80      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.57/0.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.57/0.80  thf('43', plain,
% 0.57/0.80      (![X0 : $i]:
% 0.57/0.80         ((k1_xboole_0) = (k3_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_B @ X0)))),
% 0.57/0.80      inference('demod', [status(thm)], ['30', '41', '42'])).
% 0.57/0.80  thf('44', plain,
% 0.57/0.80      (![X4 : $i, X6 : $i]:
% 0.57/0.80         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 0.57/0.80      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.57/0.80  thf('45', plain,
% 0.57/0.80      (![X0 : $i]:
% 0.57/0.80         (((k1_xboole_0) != (k1_xboole_0))
% 0.57/0.80          | (r1_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_B @ X0)))),
% 0.57/0.80      inference('sup-', [status(thm)], ['43', '44'])).
% 0.57/0.80  thf('46', plain,
% 0.57/0.80      (![X0 : $i]: (r1_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_B @ X0))),
% 0.57/0.80      inference('simplify', [status(thm)], ['45'])).
% 0.57/0.80  thf('47', plain,
% 0.57/0.80      (![X0 : $i]: (r1_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_B @ X0))),
% 0.57/0.80      inference('sup+', [status(thm)], ['5', '46'])).
% 0.57/0.80  thf('48', plain,
% 0.57/0.80      (![X0 : $i]: (r1_xboole_0 @ sk_C @ (k3_xboole_0 @ X0 @ sk_B))),
% 0.57/0.80      inference('sup+', [status(thm)], ['4', '47'])).
% 0.57/0.80  thf('49', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 0.57/0.80      inference('sup+', [status(thm)], ['3', '48'])).
% 0.57/0.80  thf('50', plain,
% 0.57/0.80      (![X4 : $i, X5 : $i]:
% 0.57/0.80         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.57/0.80      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.57/0.80  thf('51', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.57/0.80      inference('sup-', [status(thm)], ['49', '50'])).
% 0.57/0.80  thf('52', plain,
% 0.57/0.80      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.57/0.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.57/0.80  thf('53', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.57/0.80      inference('demod', [status(thm)], ['51', '52'])).
% 0.57/0.80  thf('54', plain,
% 0.57/0.80      (![X4 : $i, X6 : $i]:
% 0.57/0.80         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 0.57/0.80      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.57/0.80  thf('55', plain,
% 0.57/0.80      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_C))),
% 0.57/0.80      inference('sup-', [status(thm)], ['53', '54'])).
% 0.57/0.80  thf('56', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.57/0.80      inference('simplify', [status(thm)], ['55'])).
% 0.57/0.80  thf('57', plain, ($false), inference('demod', [status(thm)], ['0', '56'])).
% 0.57/0.80  
% 0.57/0.80  % SZS output end Refutation
% 0.57/0.80  
% 0.57/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
