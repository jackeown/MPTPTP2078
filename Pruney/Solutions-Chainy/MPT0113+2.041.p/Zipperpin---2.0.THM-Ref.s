%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hesljM6y31

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:34 EST 2020

% Result     : Theorem 0.62s
% Output     : Refutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 197 expanded)
%              Number of leaves         :   23 (  70 expanded)
%              Depth                    :   16
%              Number of atoms          :  551 (1320 expanded)
%              Number of equality atoms :   54 ( 128 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t106_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
       => ( ( r1_tarski @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t106_xboole_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
   <= ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X23 @ X24 ) @ X24 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
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

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('9',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('12',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('14',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k3_xboole_0 @ X7 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C ) ) )
      = ( k3_xboole_0 @ sk_A @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','16'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('18',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('19',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('25',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ X25 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X23 @ X24 ) @ X24 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','32'])).

thf('34',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup+',[status(thm)],['10','36'])).

thf('38',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('41',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','41'])).

thf('43',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t50_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('44',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ ( k3_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t50_xboole_1])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('45',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('46',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ ( k3_xboole_0 @ X19 @ X21 ) ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('48',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf('51',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['43','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','32'])).

thf('55',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('57',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('59',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['51','52','57','62'])).

thf('64',plain,(
    $false ),
    inference(demod,[status(thm)],['42','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hesljM6y31
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:19:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.62/0.87  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.62/0.87  % Solved by: fo/fo7.sh
% 0.62/0.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.62/0.87  % done 886 iterations in 0.411s
% 0.62/0.87  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.62/0.87  % SZS output start Refutation
% 0.62/0.87  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.62/0.87  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.62/0.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.62/0.87  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.62/0.87  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.62/0.87  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.62/0.87  thf(sk_C_type, type, sk_C: $i).
% 0.62/0.87  thf(sk_A_type, type, sk_A: $i).
% 0.62/0.87  thf(sk_B_type, type, sk_B: $i).
% 0.62/0.87  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.62/0.87  thf(t106_xboole_1, conjecture,
% 0.62/0.87    (![A:$i,B:$i,C:$i]:
% 0.62/0.87     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.62/0.87       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.62/0.87  thf(zf_stmt_0, negated_conjecture,
% 0.62/0.87    (~( ![A:$i,B:$i,C:$i]:
% 0.62/0.87        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.62/0.87          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 0.62/0.87    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 0.62/0.87  thf('0', plain,
% 0.62/0.87      ((~ (r1_tarski @ sk_A @ sk_B) | ~ (r1_xboole_0 @ sk_A @ sk_C))),
% 0.62/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.87  thf('1', plain,
% 0.62/0.87      ((~ (r1_tarski @ sk_A @ sk_B)) <= (~ ((r1_tarski @ sk_A @ sk_B)))),
% 0.62/0.87      inference('split', [status(esa)], ['0'])).
% 0.62/0.87  thf(t79_xboole_1, axiom,
% 0.62/0.87    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.62/0.87  thf('2', plain,
% 0.62/0.87      (![X23 : $i, X24 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X23 @ X24) @ X24)),
% 0.62/0.87      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.62/0.87  thf(d7_xboole_0, axiom,
% 0.62/0.87    (![A:$i,B:$i]:
% 0.62/0.87     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.62/0.87       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.62/0.87  thf('3', plain,
% 0.62/0.87      (![X2 : $i, X3 : $i]:
% 0.62/0.87         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.62/0.87      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.62/0.87  thf('4', plain,
% 0.62/0.87      (![X0 : $i, X1 : $i]:
% 0.62/0.87         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.62/0.87      inference('sup-', [status(thm)], ['2', '3'])).
% 0.62/0.87  thf(commutativity_k3_xboole_0, axiom,
% 0.62/0.87    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.62/0.87  thf('5', plain,
% 0.62/0.87      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.62/0.87      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.62/0.87  thf('6', plain,
% 0.62/0.87      (![X0 : $i, X1 : $i]:
% 0.62/0.87         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.62/0.87      inference('demod', [status(thm)], ['4', '5'])).
% 0.62/0.87  thf(t100_xboole_1, axiom,
% 0.62/0.87    (![A:$i,B:$i]:
% 0.62/0.87     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.62/0.87  thf('7', plain,
% 0.62/0.87      (![X5 : $i, X6 : $i]:
% 0.62/0.87         ((k4_xboole_0 @ X5 @ X6)
% 0.62/0.87           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.62/0.87      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.62/0.87  thf('8', plain,
% 0.62/0.87      (![X0 : $i, X1 : $i]:
% 0.62/0.87         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.62/0.87           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.62/0.87      inference('sup+', [status(thm)], ['6', '7'])).
% 0.62/0.87  thf(t5_boole, axiom,
% 0.62/0.87    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.62/0.87  thf('9', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.62/0.87      inference('cnf', [status(esa)], [t5_boole])).
% 0.62/0.87  thf('10', plain,
% 0.62/0.87      (![X0 : $i, X1 : $i]:
% 0.62/0.87         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.62/0.87      inference('demod', [status(thm)], ['8', '9'])).
% 0.62/0.87  thf('11', plain,
% 0.62/0.87      (![X0 : $i, X1 : $i]:
% 0.62/0.87         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.62/0.87      inference('demod', [status(thm)], ['4', '5'])).
% 0.62/0.87  thf('12', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.62/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.87  thf(t28_xboole_1, axiom,
% 0.62/0.87    (![A:$i,B:$i]:
% 0.62/0.87     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.62/0.87  thf('13', plain,
% 0.62/0.87      (![X14 : $i, X15 : $i]:
% 0.62/0.87         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 0.62/0.87      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.62/0.87  thf('14', plain,
% 0.62/0.87      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.62/0.87      inference('sup-', [status(thm)], ['12', '13'])).
% 0.62/0.87  thf(t16_xboole_1, axiom,
% 0.62/0.87    (![A:$i,B:$i,C:$i]:
% 0.62/0.87     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.62/0.87       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.62/0.87  thf('15', plain,
% 0.62/0.87      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.62/0.87         ((k3_xboole_0 @ (k3_xboole_0 @ X7 @ X8) @ X9)
% 0.62/0.87           = (k3_xboole_0 @ X7 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.62/0.87      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.62/0.87  thf('16', plain,
% 0.62/0.87      (![X0 : $i]:
% 0.62/0.87         ((k3_xboole_0 @ sk_A @ X0)
% 0.62/0.87           = (k3_xboole_0 @ sk_A @ 
% 0.62/0.87              (k3_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ X0)))),
% 0.62/0.87      inference('sup+', [status(thm)], ['14', '15'])).
% 0.62/0.87  thf('17', plain,
% 0.62/0.87      (![X0 : $i]:
% 0.62/0.87         ((k3_xboole_0 @ sk_A @ 
% 0.62/0.87           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C)))
% 0.62/0.87           = (k3_xboole_0 @ sk_A @ k1_xboole_0))),
% 0.62/0.87      inference('sup+', [status(thm)], ['11', '16'])).
% 0.62/0.87  thf(t21_xboole_1, axiom,
% 0.62/0.87    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.62/0.87  thf('18', plain,
% 0.62/0.87      (![X12 : $i, X13 : $i]:
% 0.62/0.87         ((k3_xboole_0 @ X12 @ (k2_xboole_0 @ X12 @ X13)) = (X12))),
% 0.62/0.87      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.62/0.87  thf(t17_xboole_1, axiom,
% 0.62/0.87    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.62/0.87  thf('19', plain,
% 0.62/0.87      (![X10 : $i, X11 : $i]: (r1_tarski @ (k3_xboole_0 @ X10 @ X11) @ X10)),
% 0.62/0.87      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.62/0.87  thf('20', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.62/0.87      inference('sup+', [status(thm)], ['18', '19'])).
% 0.62/0.87  thf('21', plain,
% 0.62/0.87      (![X14 : $i, X15 : $i]:
% 0.62/0.87         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 0.62/0.87      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.62/0.87  thf('22', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.62/0.87      inference('sup-', [status(thm)], ['20', '21'])).
% 0.62/0.87  thf('23', plain,
% 0.62/0.87      (![X5 : $i, X6 : $i]:
% 0.62/0.87         ((k4_xboole_0 @ X5 @ X6)
% 0.62/0.87           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.62/0.87      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.62/0.87  thf('24', plain,
% 0.62/0.87      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.62/0.87      inference('sup+', [status(thm)], ['22', '23'])).
% 0.62/0.87  thf(t92_xboole_1, axiom,
% 0.62/0.87    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.62/0.87  thf('25', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ X25) = (k1_xboole_0))),
% 0.62/0.87      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.62/0.87  thf('26', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.62/0.87      inference('demod', [status(thm)], ['24', '25'])).
% 0.62/0.87  thf('27', plain,
% 0.62/0.87      (![X23 : $i, X24 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X23 @ X24) @ X24)),
% 0.62/0.87      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.62/0.87  thf('28', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.62/0.87      inference('sup+', [status(thm)], ['26', '27'])).
% 0.62/0.87  thf('29', plain,
% 0.62/0.87      (![X2 : $i, X3 : $i]:
% 0.62/0.87         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.62/0.87      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.62/0.87  thf('30', plain,
% 0.62/0.87      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.62/0.87      inference('sup-', [status(thm)], ['28', '29'])).
% 0.62/0.87  thf('31', plain,
% 0.62/0.87      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.62/0.87      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.62/0.87  thf('32', plain,
% 0.62/0.87      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.62/0.87      inference('sup+', [status(thm)], ['30', '31'])).
% 0.62/0.87  thf('33', plain,
% 0.62/0.87      (![X0 : $i]:
% 0.62/0.87         ((k3_xboole_0 @ sk_A @ 
% 0.62/0.87           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C))) = (k1_xboole_0))),
% 0.62/0.87      inference('demod', [status(thm)], ['17', '32'])).
% 0.62/0.87  thf('34', plain,
% 0.62/0.87      (![X2 : $i, X4 : $i]:
% 0.62/0.87         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.62/0.87      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.62/0.87  thf('35', plain,
% 0.62/0.87      (![X0 : $i]:
% 0.62/0.87         (((k1_xboole_0) != (k1_xboole_0))
% 0.62/0.87          | (r1_xboole_0 @ sk_A @ 
% 0.62/0.87             (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C))))),
% 0.62/0.87      inference('sup-', [status(thm)], ['33', '34'])).
% 0.62/0.87  thf('36', plain,
% 0.62/0.87      (![X0 : $i]:
% 0.62/0.87         (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.62/0.87      inference('simplify', [status(thm)], ['35'])).
% 0.62/0.87  thf('37', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.62/0.87      inference('sup+', [status(thm)], ['10', '36'])).
% 0.62/0.87  thf('38', plain,
% 0.62/0.87      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.62/0.87      inference('split', [status(esa)], ['0'])).
% 0.62/0.87  thf('39', plain, (((r1_xboole_0 @ sk_A @ sk_C))),
% 0.62/0.87      inference('sup-', [status(thm)], ['37', '38'])).
% 0.62/0.87  thf('40', plain,
% 0.62/0.87      (~ ((r1_tarski @ sk_A @ sk_B)) | ~ ((r1_xboole_0 @ sk_A @ sk_C))),
% 0.62/0.87      inference('split', [status(esa)], ['0'])).
% 0.62/0.87  thf('41', plain, (~ ((r1_tarski @ sk_A @ sk_B))),
% 0.62/0.87      inference('sat_resolution*', [status(thm)], ['39', '40'])).
% 0.62/0.87  thf('42', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.62/0.87      inference('simpl_trail', [status(thm)], ['1', '41'])).
% 0.62/0.87  thf('43', plain,
% 0.62/0.87      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.62/0.87      inference('sup-', [status(thm)], ['12', '13'])).
% 0.62/0.87  thf(t50_xboole_1, axiom,
% 0.62/0.87    (![A:$i,B:$i,C:$i]:
% 0.62/0.87     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.62/0.87       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.62/0.87  thf('44', plain,
% 0.62/0.87      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.62/0.87         ((k3_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 0.62/0.87           = (k4_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ 
% 0.62/0.87              (k3_xboole_0 @ X19 @ X21)))),
% 0.62/0.87      inference('cnf', [status(esa)], [t50_xboole_1])).
% 0.62/0.87  thf(t49_xboole_1, axiom,
% 0.62/0.87    (![A:$i,B:$i,C:$i]:
% 0.62/0.87     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.62/0.87       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.62/0.87  thf('45', plain,
% 0.62/0.87      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.62/0.87         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 0.62/0.87           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 0.62/0.87      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.62/0.87  thf('46', plain,
% 0.62/0.87      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.62/0.87         ((k3_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 0.62/0.87           = (k3_xboole_0 @ X19 @ 
% 0.62/0.87              (k4_xboole_0 @ X20 @ (k3_xboole_0 @ X19 @ X21))))),
% 0.62/0.87      inference('demod', [status(thm)], ['44', '45'])).
% 0.62/0.87  thf('47', plain,
% 0.62/0.87      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.62/0.87      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.62/0.87  thf('48', plain,
% 0.62/0.87      (![X10 : $i, X11 : $i]: (r1_tarski @ (k3_xboole_0 @ X10 @ X11) @ X10)),
% 0.62/0.87      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.62/0.87  thf('49', plain,
% 0.62/0.87      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.62/0.87      inference('sup+', [status(thm)], ['47', '48'])).
% 0.62/0.87  thf('50', plain,
% 0.62/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.87         (r1_tarski @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 0.62/0.87          (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ X0)))),
% 0.62/0.87      inference('sup+', [status(thm)], ['46', '49'])).
% 0.62/0.87  thf('51', plain,
% 0.62/0.87      ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_C)))),
% 0.62/0.87      inference('sup+', [status(thm)], ['43', '50'])).
% 0.62/0.87  thf('52', plain,
% 0.62/0.87      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.62/0.87      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.62/0.87  thf('53', plain,
% 0.62/0.87      (![X0 : $i, X1 : $i]:
% 0.62/0.87         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.62/0.87      inference('demod', [status(thm)], ['8', '9'])).
% 0.62/0.87  thf('54', plain,
% 0.62/0.87      (![X0 : $i]:
% 0.62/0.87         ((k3_xboole_0 @ sk_A @ 
% 0.62/0.87           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C))) = (k1_xboole_0))),
% 0.62/0.87      inference('demod', [status(thm)], ['17', '32'])).
% 0.62/0.87  thf('55', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.62/0.87      inference('sup+', [status(thm)], ['53', '54'])).
% 0.62/0.87  thf('56', plain,
% 0.62/0.87      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.62/0.87      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.62/0.87  thf('57', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.62/0.87      inference('demod', [status(thm)], ['55', '56'])).
% 0.62/0.87  thf('58', plain,
% 0.62/0.87      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.62/0.87      inference('sup+', [status(thm)], ['30', '31'])).
% 0.62/0.87  thf('59', plain,
% 0.62/0.87      (![X5 : $i, X6 : $i]:
% 0.62/0.87         ((k4_xboole_0 @ X5 @ X6)
% 0.62/0.87           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.62/0.87      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.62/0.87  thf('60', plain,
% 0.62/0.87      (![X0 : $i]:
% 0.62/0.87         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.62/0.87      inference('sup+', [status(thm)], ['58', '59'])).
% 0.62/0.87  thf('61', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.62/0.87      inference('cnf', [status(esa)], [t5_boole])).
% 0.62/0.87  thf('62', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.62/0.87      inference('demod', [status(thm)], ['60', '61'])).
% 0.62/0.87  thf('63', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.62/0.87      inference('demod', [status(thm)], ['51', '52', '57', '62'])).
% 0.62/0.87  thf('64', plain, ($false), inference('demod', [status(thm)], ['42', '63'])).
% 0.62/0.87  
% 0.62/0.87  % SZS output end Refutation
% 0.62/0.87  
% 0.70/0.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
