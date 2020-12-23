%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.j0wJvUq2Rm

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:28 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 154 expanded)
%              Number of leaves         :   23 (  57 expanded)
%              Depth                    :   12
%              Number of atoms          :  517 ( 971 expanded)
%              Number of equality atoms :   48 (  88 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    | ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
   <= ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('2',plain,(
    ! [X22: $i] :
      ( ( k4_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('3',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r1_tarski @ X32 @ X33 )
      | ( r1_xboole_0 @ X32 @ ( k4_xboole_0 @ X34 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('11',plain,(
    ! [X27: $i] :
      ( r1_xboole_0 @ X27 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('12',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X22: $i] :
      ( ( k4_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['10','17'])).

thf('19',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r1_tarski @ X32 @ X33 )
      | ( r1_xboole_0 @ X32 @ ( k4_xboole_0 @ X34 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C_1 )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('24',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','26'])).

thf('28',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('29',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('30',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('31',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) )
    = sk_A ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('33',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) )
      = ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('35',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) @ ( k5_xboole_0 @ sk_A @ sk_A ) )
    = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('38',plain,
    ( ( k2_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_A ) @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X22: $i] :
      ( ( k4_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('40',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('43',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','46','47'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('52',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X25 @ X26 ) @ ( k4_xboole_0 @ X25 @ X26 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('54',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X25 @ X26 ) @ ( k3_xboole_0 @ X25 @ X26 ) )
      = X25 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C_1 )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['38','48','57'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('59',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X13 @ X15 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['28','60'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['27','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.j0wJvUq2Rm
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:09:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.37/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.57  % Solved by: fo/fo7.sh
% 0.37/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.57  % done 459 iterations in 0.110s
% 0.37/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.57  % SZS output start Refutation
% 0.37/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.57  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.57  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.37/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.57  thf(t106_xboole_1, conjecture,
% 0.37/0.57    (![A:$i,B:$i,C:$i]:
% 0.37/0.57     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.37/0.57       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.37/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.57        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.37/0.57          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 0.37/0.57    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 0.37/0.57  thf('0', plain,
% 0.37/0.57      ((~ (r1_tarski @ sk_A @ sk_B) | ~ (r1_xboole_0 @ sk_A @ sk_C_1))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('1', plain,
% 0.37/0.57      ((~ (r1_tarski @ sk_A @ sk_B)) <= (~ ((r1_tarski @ sk_A @ sk_B)))),
% 0.37/0.57      inference('split', [status(esa)], ['0'])).
% 0.37/0.57  thf(t3_boole, axiom,
% 0.37/0.57    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.57  thf('2', plain, (![X22 : $i]: ((k4_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.37/0.57      inference('cnf', [status(esa)], [t3_boole])).
% 0.37/0.57  thf(t36_xboole_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.37/0.57  thf('3', plain,
% 0.37/0.57      (![X18 : $i, X19 : $i]: (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X18)),
% 0.37/0.57      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.37/0.57  thf('4', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.37/0.57      inference('sup+', [status(thm)], ['2', '3'])).
% 0.37/0.57  thf(t85_xboole_1, axiom,
% 0.37/0.57    (![A:$i,B:$i,C:$i]:
% 0.37/0.57     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.37/0.57  thf('5', plain,
% 0.37/0.57      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.37/0.57         (~ (r1_tarski @ X32 @ X33)
% 0.37/0.57          | (r1_xboole_0 @ X32 @ (k4_xboole_0 @ X34 @ X33)))),
% 0.37/0.57      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.37/0.57  thf('6', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['4', '5'])).
% 0.37/0.57  thf(d7_xboole_0, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.37/0.57       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.37/0.57  thf('7', plain,
% 0.37/0.57      (![X4 : $i, X5 : $i]:
% 0.37/0.57         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.37/0.57      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.37/0.57  thf('8', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.57  thf(t100_xboole_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.57  thf('9', plain,
% 0.37/0.57      (![X11 : $i, X12 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X11 @ X12)
% 0.37/0.57           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.37/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.57  thf('10', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.37/0.57           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.57      inference('sup+', [status(thm)], ['8', '9'])).
% 0.37/0.57  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.37/0.57  thf('11', plain, (![X27 : $i]: (r1_xboole_0 @ X27 @ k1_xboole_0)),
% 0.37/0.57      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.37/0.57  thf('12', plain,
% 0.37/0.57      (![X4 : $i, X5 : $i]:
% 0.37/0.57         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.37/0.57      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.37/0.57  thf('13', plain,
% 0.37/0.57      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.57  thf('14', plain,
% 0.37/0.57      (![X11 : $i, X12 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X11 @ X12)
% 0.37/0.57           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.37/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.57  thf('15', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.57      inference('sup+', [status(thm)], ['13', '14'])).
% 0.37/0.57  thf('16', plain, (![X22 : $i]: ((k4_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.37/0.57      inference('cnf', [status(esa)], [t3_boole])).
% 0.37/0.57  thf('17', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.37/0.57      inference('sup+', [status(thm)], ['15', '16'])).
% 0.37/0.57  thf('18', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.37/0.57      inference('demod', [status(thm)], ['10', '17'])).
% 0.37/0.57  thf('19', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('20', plain,
% 0.37/0.57      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.37/0.57         (~ (r1_tarski @ X32 @ X33)
% 0.37/0.57          | (r1_xboole_0 @ X32 @ (k4_xboole_0 @ X34 @ X33)))),
% 0.37/0.57      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.37/0.57  thf('21', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (r1_xboole_0 @ sk_A @ 
% 0.37/0.57          (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C_1)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['19', '20'])).
% 0.37/0.57  thf('22', plain, ((r1_xboole_0 @ sk_A @ sk_C_1)),
% 0.37/0.57      inference('sup+', [status(thm)], ['18', '21'])).
% 0.37/0.57  thf('23', plain,
% 0.37/0.57      ((~ (r1_xboole_0 @ sk_A @ sk_C_1)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 0.37/0.57      inference('split', [status(esa)], ['0'])).
% 0.37/0.57  thf('24', plain, (((r1_xboole_0 @ sk_A @ sk_C_1))),
% 0.37/0.57      inference('sup-', [status(thm)], ['22', '23'])).
% 0.37/0.57  thf('25', plain,
% 0.37/0.57      (~ ((r1_tarski @ sk_A @ sk_B)) | ~ ((r1_xboole_0 @ sk_A @ sk_C_1))),
% 0.37/0.57      inference('split', [status(esa)], ['0'])).
% 0.37/0.57  thf('26', plain, (~ ((r1_tarski @ sk_A @ sk_B))),
% 0.37/0.57      inference('sat_resolution*', [status(thm)], ['24', '25'])).
% 0.37/0.57  thf('27', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.37/0.57      inference('simpl_trail', [status(thm)], ['1', '26'])).
% 0.37/0.57  thf('28', plain,
% 0.37/0.57      (![X18 : $i, X19 : $i]: (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X18)),
% 0.37/0.57      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.37/0.57  thf('29', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(t28_xboole_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.37/0.57  thf('30', plain,
% 0.37/0.57      (![X16 : $i, X17 : $i]:
% 0.37/0.57         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.37/0.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.57  thf('31', plain,
% 0.37/0.57      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1)) = (sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['29', '30'])).
% 0.37/0.57  thf('32', plain,
% 0.37/0.57      (![X11 : $i, X12 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X11 @ X12)
% 0.37/0.57           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.37/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.57  thf('33', plain,
% 0.37/0.57      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1))
% 0.37/0.57         = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.37/0.57      inference('sup+', [status(thm)], ['31', '32'])).
% 0.37/0.57  thf(t39_xboole_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.37/0.57  thf('34', plain,
% 0.37/0.57      (![X20 : $i, X21 : $i]:
% 0.37/0.57         ((k2_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20))
% 0.37/0.57           = (k2_xboole_0 @ X20 @ X21))),
% 0.37/0.57      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.37/0.57  thf('35', plain,
% 0.37/0.57      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C_1) @ 
% 0.37/0.57         (k5_xboole_0 @ sk_A @ sk_A))
% 0.37/0.57         = (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C_1) @ sk_A))),
% 0.37/0.57      inference('sup+', [status(thm)], ['33', '34'])).
% 0.37/0.57  thf(commutativity_k2_xboole_0, axiom,
% 0.37/0.57    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.37/0.57  thf('36', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.57      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.37/0.57  thf('37', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.57      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.37/0.57  thf('38', plain,
% 0.37/0.57      (((k2_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_A) @ 
% 0.37/0.57         (k4_xboole_0 @ sk_B @ sk_C_1))
% 0.37/0.57         = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1)))),
% 0.37/0.57      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.37/0.57  thf('39', plain, (![X22 : $i]: ((k4_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.37/0.57      inference('cnf', [status(esa)], [t3_boole])).
% 0.37/0.57  thf(t48_xboole_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.37/0.57  thf('40', plain,
% 0.37/0.57      (![X23 : $i, X24 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 0.37/0.57           = (k3_xboole_0 @ X23 @ X24))),
% 0.37/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.57  thf('41', plain,
% 0.37/0.57      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.57      inference('sup+', [status(thm)], ['39', '40'])).
% 0.37/0.57  thf('42', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.37/0.57      inference('sup+', [status(thm)], ['2', '3'])).
% 0.37/0.57  thf('43', plain,
% 0.37/0.57      (![X16 : $i, X17 : $i]:
% 0.37/0.57         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.37/0.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.57  thf('44', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['42', '43'])).
% 0.37/0.57  thf('45', plain,
% 0.37/0.57      (![X11 : $i, X12 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X11 @ X12)
% 0.37/0.57           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.37/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.57  thf('46', plain,
% 0.37/0.57      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.57      inference('sup+', [status(thm)], ['44', '45'])).
% 0.37/0.57  thf('47', plain,
% 0.37/0.57      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.57  thf('48', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.57      inference('demod', [status(thm)], ['41', '46', '47'])).
% 0.37/0.57  thf('49', plain,
% 0.37/0.57      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.57      inference('sup+', [status(thm)], ['44', '45'])).
% 0.37/0.57  thf('50', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.57      inference('demod', [status(thm)], ['41', '46', '47'])).
% 0.37/0.57  thf('51', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.57      inference('demod', [status(thm)], ['49', '50'])).
% 0.37/0.57  thf(t51_xboole_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.37/0.57       ( A ) ))).
% 0.37/0.57  thf('52', plain,
% 0.37/0.57      (![X25 : $i, X26 : $i]:
% 0.37/0.57         ((k2_xboole_0 @ (k3_xboole_0 @ X25 @ X26) @ (k4_xboole_0 @ X25 @ X26))
% 0.37/0.57           = (X25))),
% 0.37/0.57      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.37/0.57  thf('53', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.57      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.37/0.57  thf('54', plain,
% 0.37/0.57      (![X25 : $i, X26 : $i]:
% 0.37/0.57         ((k2_xboole_0 @ (k4_xboole_0 @ X25 @ X26) @ (k3_xboole_0 @ X25 @ X26))
% 0.37/0.57           = (X25))),
% 0.37/0.57      inference('demod', [status(thm)], ['52', '53'])).
% 0.37/0.57  thf('55', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X0 @ X0)) = (X0))),
% 0.37/0.57      inference('sup+', [status(thm)], ['51', '54'])).
% 0.37/0.57  thf('56', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['42', '43'])).
% 0.37/0.57  thf('57', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.37/0.57      inference('demod', [status(thm)], ['55', '56'])).
% 0.37/0.57  thf('58', plain,
% 0.37/0.57      (((k4_xboole_0 @ sk_B @ sk_C_1)
% 0.37/0.57         = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1)))),
% 0.37/0.57      inference('demod', [status(thm)], ['38', '48', '57'])).
% 0.37/0.57  thf(t11_xboole_1, axiom,
% 0.37/0.57    (![A:$i,B:$i,C:$i]:
% 0.37/0.57     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.37/0.57  thf('59', plain,
% 0.37/0.57      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.37/0.57         ((r1_tarski @ X13 @ X14)
% 0.37/0.57          | ~ (r1_tarski @ (k2_xboole_0 @ X13 @ X15) @ X14))),
% 0.37/0.57      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.37/0.57  thf('60', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (~ (r1_tarski @ (k4_xboole_0 @ sk_B @ sk_C_1) @ X0)
% 0.37/0.57          | (r1_tarski @ sk_A @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['58', '59'])).
% 0.37/0.57  thf('61', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.37/0.57      inference('sup-', [status(thm)], ['28', '60'])).
% 0.37/0.57  thf('62', plain, ($false), inference('demod', [status(thm)], ['27', '61'])).
% 0.37/0.57  
% 0.37/0.57  % SZS output end Refutation
% 0.37/0.57  
% 0.37/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
