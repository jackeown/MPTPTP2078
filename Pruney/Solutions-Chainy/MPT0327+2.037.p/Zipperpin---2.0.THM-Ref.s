%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.w1tiOXNCqs

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:54 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 165 expanded)
%              Number of leaves         :   24 (  60 expanded)
%              Depth                    :   11
%              Number of atoms          :  573 (1244 expanded)
%              Number of equality atoms :   61 ( 126 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t140_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k2_xboole_0 @ ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t140_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('1',plain,(
    ! [X37: $i,X39: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X37 ) @ X39 )
      | ~ ( r2_hidden @ X37 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('2',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('6',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('8',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('14',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('18',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['8','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X25 @ X26 ) @ ( k3_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('23',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('24',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ X25 @ ( k5_xboole_0 @ X26 @ ( k3_xboole_0 @ X25 @ X26 ) ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['20','27'])).

thf('29',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('30',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('31',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('33',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('35',plain,
    ( ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    = ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ sk_B ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('38',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('44',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('48',plain,
    ( ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['28','35','36','46','47'])).

thf('49',plain,(
    ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('51',plain,(
    ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    = ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ sk_B ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('53',plain,(
    ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ sk_B )
 != sk_B ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['48','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.w1tiOXNCqs
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:38:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.49/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.49/0.67  % Solved by: fo/fo7.sh
% 0.49/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.67  % done 558 iterations in 0.213s
% 0.49/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.49/0.67  % SZS output start Refutation
% 0.49/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.49/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.49/0.67  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.49/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.49/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.49/0.67  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.49/0.67  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.49/0.67  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.49/0.67  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.49/0.67  thf(t140_zfmisc_1, conjecture,
% 0.49/0.67    (![A:$i,B:$i]:
% 0.49/0.67     ( ( r2_hidden @ A @ B ) =>
% 0.49/0.67       ( ( k2_xboole_0 @
% 0.49/0.67           ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.49/0.67         ( B ) ) ))).
% 0.49/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.67    (~( ![A:$i,B:$i]:
% 0.49/0.67        ( ( r2_hidden @ A @ B ) =>
% 0.49/0.67          ( ( k2_xboole_0 @
% 0.49/0.67              ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.49/0.67            ( B ) ) ) )),
% 0.49/0.67    inference('cnf.neg', [status(esa)], [t140_zfmisc_1])).
% 0.49/0.67  thf('0', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf(l1_zfmisc_1, axiom,
% 0.49/0.67    (![A:$i,B:$i]:
% 0.49/0.67     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.49/0.67  thf('1', plain,
% 0.49/0.67      (![X37 : $i, X39 : $i]:
% 0.49/0.67         ((r1_tarski @ (k1_tarski @ X37) @ X39) | ~ (r2_hidden @ X37 @ X39))),
% 0.49/0.67      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.49/0.67  thf('2', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.49/0.67      inference('sup-', [status(thm)], ['0', '1'])).
% 0.49/0.67  thf(t28_xboole_1, axiom,
% 0.49/0.67    (![A:$i,B:$i]:
% 0.49/0.67     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.49/0.67  thf('3', plain,
% 0.49/0.67      (![X10 : $i, X11 : $i]:
% 0.49/0.67         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.49/0.67      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.49/0.67  thf('4', plain,
% 0.49/0.67      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))),
% 0.49/0.67      inference('sup-', [status(thm)], ['2', '3'])).
% 0.49/0.67  thf(commutativity_k3_xboole_0, axiom,
% 0.49/0.67    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.49/0.67  thf('5', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.49/0.67      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.49/0.67  thf('6', plain,
% 0.49/0.67      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.49/0.67      inference('demod', [status(thm)], ['4', '5'])).
% 0.49/0.67  thf(t100_xboole_1, axiom,
% 0.49/0.67    (![A:$i,B:$i]:
% 0.49/0.67     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.49/0.67  thf('7', plain,
% 0.49/0.67      (![X8 : $i, X9 : $i]:
% 0.49/0.67         ((k4_xboole_0 @ X8 @ X9)
% 0.49/0.67           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.49/0.67      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.49/0.67  thf('8', plain,
% 0.49/0.67      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.49/0.67         = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.49/0.67      inference('sup+', [status(thm)], ['6', '7'])).
% 0.49/0.67  thf(t48_xboole_1, axiom,
% 0.49/0.67    (![A:$i,B:$i]:
% 0.49/0.67     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.49/0.67  thf('9', plain,
% 0.49/0.67      (![X16 : $i, X17 : $i]:
% 0.49/0.67         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.49/0.67           = (k3_xboole_0 @ X16 @ X17))),
% 0.49/0.67      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.49/0.67  thf(t36_xboole_1, axiom,
% 0.49/0.67    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.49/0.67  thf('10', plain,
% 0.49/0.67      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 0.49/0.67      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.49/0.67  thf(l32_xboole_1, axiom,
% 0.49/0.67    (![A:$i,B:$i]:
% 0.49/0.67     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.49/0.67  thf('11', plain,
% 0.49/0.67      (![X5 : $i, X7 : $i]:
% 0.49/0.67         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.49/0.67      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.49/0.67  thf('12', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.49/0.67      inference('sup-', [status(thm)], ['10', '11'])).
% 0.49/0.67  thf('13', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 0.49/0.67      inference('sup+', [status(thm)], ['9', '12'])).
% 0.49/0.67  thf(t49_xboole_1, axiom,
% 0.49/0.67    (![A:$i,B:$i,C:$i]:
% 0.49/0.67     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.49/0.67       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.49/0.67  thf('14', plain,
% 0.49/0.67      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.49/0.67         ((k3_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 0.49/0.67           = (k4_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X20))),
% 0.49/0.67      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.49/0.67  thf('15', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.49/0.67      inference('demod', [status(thm)], ['13', '14'])).
% 0.49/0.67  thf('16', plain,
% 0.49/0.67      (![X8 : $i, X9 : $i]:
% 0.49/0.67         ((k4_xboole_0 @ X8 @ X9)
% 0.49/0.67           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.49/0.67      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.49/0.67  thf('17', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.49/0.67           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.49/0.67      inference('sup+', [status(thm)], ['15', '16'])).
% 0.49/0.67  thf(t5_boole, axiom,
% 0.49/0.67    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.49/0.67  thf('18', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 0.49/0.67      inference('cnf', [status(esa)], [t5_boole])).
% 0.49/0.67  thf('19', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.49/0.67      inference('demod', [status(thm)], ['17', '18'])).
% 0.49/0.67  thf('20', plain,
% 0.49/0.67      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.49/0.67         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) = (k1_tarski @ sk_A))),
% 0.49/0.67      inference('sup+', [status(thm)], ['8', '19'])).
% 0.49/0.67  thf('21', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.49/0.67      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.49/0.67  thf(t94_xboole_1, axiom,
% 0.49/0.67    (![A:$i,B:$i]:
% 0.49/0.67     ( ( k2_xboole_0 @ A @ B ) =
% 0.49/0.67       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.49/0.67  thf('22', plain,
% 0.49/0.67      (![X25 : $i, X26 : $i]:
% 0.49/0.67         ((k2_xboole_0 @ X25 @ X26)
% 0.49/0.67           = (k5_xboole_0 @ (k5_xboole_0 @ X25 @ X26) @ 
% 0.49/0.67              (k3_xboole_0 @ X25 @ X26)))),
% 0.49/0.67      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.49/0.67  thf(t91_xboole_1, axiom,
% 0.49/0.67    (![A:$i,B:$i,C:$i]:
% 0.49/0.67     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.49/0.67       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.49/0.67  thf('23', plain,
% 0.49/0.67      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.49/0.67         ((k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ X24)
% 0.49/0.67           = (k5_xboole_0 @ X22 @ (k5_xboole_0 @ X23 @ X24)))),
% 0.49/0.67      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.49/0.67  thf('24', plain,
% 0.49/0.67      (![X25 : $i, X26 : $i]:
% 0.49/0.67         ((k2_xboole_0 @ X25 @ X26)
% 0.49/0.67           = (k5_xboole_0 @ X25 @ 
% 0.49/0.67              (k5_xboole_0 @ X26 @ (k3_xboole_0 @ X25 @ X26))))),
% 0.49/0.67      inference('demod', [status(thm)], ['22', '23'])).
% 0.49/0.67  thf('25', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((k2_xboole_0 @ X0 @ X1)
% 0.49/0.67           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.49/0.67      inference('sup+', [status(thm)], ['21', '24'])).
% 0.49/0.67  thf('26', plain,
% 0.49/0.67      (![X8 : $i, X9 : $i]:
% 0.49/0.67         ((k4_xboole_0 @ X8 @ X9)
% 0.49/0.67           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.49/0.67      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.49/0.67  thf('27', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((k2_xboole_0 @ X0 @ X1)
% 0.49/0.67           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.49/0.67      inference('demod', [status(thm)], ['25', '26'])).
% 0.49/0.67  thf('28', plain,
% 0.49/0.67      (((k2_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.49/0.67         (k1_tarski @ sk_A))
% 0.49/0.67         = (k5_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.49/0.67            (k1_tarski @ sk_A)))),
% 0.49/0.67      inference('sup+', [status(thm)], ['20', '27'])).
% 0.49/0.67  thf('29', plain,
% 0.49/0.67      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.49/0.67         = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.49/0.67      inference('sup+', [status(thm)], ['6', '7'])).
% 0.49/0.67  thf('30', plain,
% 0.49/0.67      (![X16 : $i, X17 : $i]:
% 0.49/0.67         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.49/0.67           = (k3_xboole_0 @ X16 @ X17))),
% 0.49/0.67      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.49/0.67  thf('31', plain,
% 0.49/0.67      (((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.49/0.67         = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.49/0.67      inference('sup+', [status(thm)], ['29', '30'])).
% 0.49/0.67  thf('32', plain,
% 0.49/0.67      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.49/0.67      inference('demod', [status(thm)], ['4', '5'])).
% 0.49/0.67  thf('33', plain,
% 0.49/0.67      (((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.49/0.67         = (k1_tarski @ sk_A))),
% 0.49/0.67      inference('demod', [status(thm)], ['31', '32'])).
% 0.49/0.67  thf(t39_xboole_1, axiom,
% 0.49/0.67    (![A:$i,B:$i]:
% 0.49/0.67     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.49/0.67  thf('34', plain,
% 0.49/0.67      (![X14 : $i, X15 : $i]:
% 0.49/0.67         ((k2_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14))
% 0.49/0.67           = (k2_xboole_0 @ X14 @ X15))),
% 0.49/0.67      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.49/0.67  thf('35', plain,
% 0.49/0.67      (((k2_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.49/0.67         (k1_tarski @ sk_A))
% 0.49/0.67         = (k2_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ sk_B))),
% 0.49/0.67      inference('sup+', [status(thm)], ['33', '34'])).
% 0.49/0.67  thf('36', plain,
% 0.49/0.67      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.49/0.67         ((k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ X24)
% 0.49/0.67           = (k5_xboole_0 @ X22 @ (k5_xboole_0 @ X23 @ X24)))),
% 0.49/0.67      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.49/0.67  thf(d10_xboole_0, axiom,
% 0.49/0.67    (![A:$i,B:$i]:
% 0.49/0.67     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.49/0.67  thf('37', plain,
% 0.49/0.67      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.49/0.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.49/0.67  thf('38', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.49/0.67      inference('simplify', [status(thm)], ['37'])).
% 0.49/0.67  thf('39', plain,
% 0.49/0.67      (![X10 : $i, X11 : $i]:
% 0.49/0.67         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.49/0.67      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.49/0.67  thf('40', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.49/0.67      inference('sup-', [status(thm)], ['38', '39'])).
% 0.49/0.67  thf('41', plain,
% 0.49/0.67      (![X8 : $i, X9 : $i]:
% 0.49/0.67         ((k4_xboole_0 @ X8 @ X9)
% 0.49/0.67           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.49/0.67      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.49/0.67  thf('42', plain,
% 0.49/0.67      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.49/0.67      inference('sup+', [status(thm)], ['40', '41'])).
% 0.49/0.67  thf('43', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.49/0.67      inference('simplify', [status(thm)], ['37'])).
% 0.49/0.67  thf('44', plain,
% 0.49/0.67      (![X5 : $i, X7 : $i]:
% 0.49/0.67         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.49/0.67      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.49/0.67  thf('45', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.49/0.67      inference('sup-', [status(thm)], ['43', '44'])).
% 0.49/0.67  thf('46', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.49/0.67      inference('sup+', [status(thm)], ['42', '45'])).
% 0.49/0.67  thf('47', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 0.49/0.67      inference('cnf', [status(esa)], [t5_boole])).
% 0.49/0.67  thf('48', plain,
% 0.49/0.67      (((k2_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ sk_B)
% 0.49/0.67         = (sk_B))),
% 0.49/0.67      inference('demod', [status(thm)], ['28', '35', '36', '46', '47'])).
% 0.49/0.67  thf('49', plain,
% 0.49/0.67      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.49/0.67         (k1_tarski @ sk_A)) != (sk_B))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('50', plain,
% 0.49/0.67      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.49/0.67         = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.49/0.67      inference('sup+', [status(thm)], ['6', '7'])).
% 0.49/0.67  thf('51', plain,
% 0.49/0.67      (((k2_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.49/0.67         (k1_tarski @ sk_A)) != (sk_B))),
% 0.49/0.67      inference('demod', [status(thm)], ['49', '50'])).
% 0.49/0.67  thf('52', plain,
% 0.49/0.67      (((k2_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.49/0.67         (k1_tarski @ sk_A))
% 0.49/0.67         = (k2_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ sk_B))),
% 0.49/0.67      inference('sup+', [status(thm)], ['33', '34'])).
% 0.49/0.67  thf('53', plain,
% 0.49/0.67      (((k2_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ sk_B)
% 0.49/0.67         != (sk_B))),
% 0.49/0.67      inference('demod', [status(thm)], ['51', '52'])).
% 0.49/0.67  thf('54', plain, ($false),
% 0.49/0.67      inference('simplify_reflect-', [status(thm)], ['48', '53'])).
% 0.49/0.67  
% 0.49/0.67  % SZS output end Refutation
% 0.49/0.67  
% 0.49/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
