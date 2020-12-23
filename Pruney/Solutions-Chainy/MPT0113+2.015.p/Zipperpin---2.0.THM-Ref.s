%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.B7PDjwbRD7

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:30 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 147 expanded)
%              Number of leaves         :   21 (  53 expanded)
%              Depth                    :   13
%              Number of atoms          :  547 (1030 expanded)
%              Number of equality atoms :   57 (  94 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X11: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X13 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

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
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
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
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ k1_xboole_0 )
      = X25 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('12',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('14',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) )
    = sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) )
      = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ) ) ) ),
    inference('sup+',[status(thm)],['11','16'])).

thf('18',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) )
    = sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf('19',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['10','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('23',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference('sup+',[status(thm)],['20','26'])).

thf('28',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C_1 )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('29',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','31'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('33',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('34',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('41',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('44',plain,(
    ! [X29: $i] :
      ( ( k5_xboole_0 @ X29 @ X29 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('47',plain,
    ( ( k3_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('50',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X11: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X13 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('56',plain,(
    ! [X11: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X13 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X1: $i] :
      ( ( k3_xboole_0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','54','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['47','48','60'])).

thf('62',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ( ( k4_xboole_0 @ X11 @ X12 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('63',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['32','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.B7PDjwbRD7
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:24:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.36/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.61  % Solved by: fo/fo7.sh
% 0.36/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.61  % done 438 iterations in 0.166s
% 0.36/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.61  % SZS output start Refutation
% 0.36/0.61  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.36/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.61  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.36/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.61  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.36/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.61  thf(t106_xboole_1, conjecture,
% 0.36/0.61    (![A:$i,B:$i,C:$i]:
% 0.36/0.61     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.36/0.61       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.36/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.36/0.61        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.36/0.61          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 0.36/0.61    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 0.36/0.61  thf('0', plain,
% 0.36/0.61      ((~ (r1_tarski @ sk_A @ sk_B) | ~ (r1_xboole_0 @ sk_A @ sk_C_1))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('1', plain,
% 0.36/0.61      ((~ (r1_tarski @ sk_A @ sk_B)) <= (~ ((r1_tarski @ sk_A @ sk_B)))),
% 0.36/0.61      inference('split', [status(esa)], ['0'])).
% 0.36/0.61  thf(t17_xboole_1, axiom,
% 0.36/0.61    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.36/0.61  thf('2', plain,
% 0.36/0.61      (![X16 : $i, X17 : $i]: (r1_tarski @ (k3_xboole_0 @ X16 @ X17) @ X16)),
% 0.36/0.61      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.36/0.61  thf(l32_xboole_1, axiom,
% 0.36/0.61    (![A:$i,B:$i]:
% 0.36/0.61     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.61  thf('3', plain,
% 0.36/0.61      (![X11 : $i, X13 : $i]:
% 0.36/0.61         (((k4_xboole_0 @ X11 @ X13) = (k1_xboole_0))
% 0.36/0.61          | ~ (r1_tarski @ X11 @ X13))),
% 0.36/0.61      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.36/0.61  thf('4', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]:
% 0.36/0.61         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.36/0.61      inference('sup-', [status(thm)], ['2', '3'])).
% 0.36/0.61  thf(t49_xboole_1, axiom,
% 0.36/0.61    (![A:$i,B:$i,C:$i]:
% 0.36/0.61     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.36/0.61       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.36/0.61  thf('5', plain,
% 0.36/0.61      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.36/0.61         ((k3_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X24))
% 0.36/0.61           = (k4_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ X24))),
% 0.36/0.61      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.36/0.61  thf('6', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]:
% 0.36/0.61         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.36/0.61      inference('demod', [status(thm)], ['4', '5'])).
% 0.36/0.61  thf(t100_xboole_1, axiom,
% 0.36/0.61    (![A:$i,B:$i]:
% 0.36/0.61     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.36/0.61  thf('7', plain,
% 0.36/0.61      (![X14 : $i, X15 : $i]:
% 0.36/0.61         ((k4_xboole_0 @ X14 @ X15)
% 0.36/0.61           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.36/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.36/0.61  thf('8', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]:
% 0.36/0.61         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.36/0.61           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.36/0.61      inference('sup+', [status(thm)], ['6', '7'])).
% 0.36/0.61  thf(t5_boole, axiom,
% 0.36/0.61    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.36/0.61  thf('9', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ k1_xboole_0) = (X25))),
% 0.36/0.61      inference('cnf', [status(esa)], [t5_boole])).
% 0.36/0.61  thf('10', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]:
% 0.36/0.61         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.36/0.61      inference('demod', [status(thm)], ['8', '9'])).
% 0.36/0.61  thf('11', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]:
% 0.36/0.61         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.36/0.61      inference('demod', [status(thm)], ['8', '9'])).
% 0.36/0.61  thf('12', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf(t28_xboole_1, axiom,
% 0.36/0.61    (![A:$i,B:$i]:
% 0.36/0.61     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.36/0.61  thf('13', plain,
% 0.36/0.61      (![X20 : $i, X21 : $i]:
% 0.36/0.61         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 0.36/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.36/0.61  thf('14', plain,
% 0.36/0.61      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1)) = (sk_A))),
% 0.36/0.61      inference('sup-', [status(thm)], ['12', '13'])).
% 0.36/0.61  thf('15', plain,
% 0.36/0.61      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.36/0.61         ((k3_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X24))
% 0.36/0.61           = (k4_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ X24))),
% 0.36/0.61      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.36/0.61  thf('16', plain,
% 0.36/0.61      (![X0 : $i]:
% 0.36/0.61         ((k3_xboole_0 @ sk_A @ 
% 0.36/0.61           (k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C_1) @ X0))
% 0.36/0.61           = (k4_xboole_0 @ sk_A @ X0))),
% 0.36/0.61      inference('sup+', [status(thm)], ['14', '15'])).
% 0.36/0.61  thf('17', plain,
% 0.36/0.61      (![X0 : $i]:
% 0.36/0.61         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1))
% 0.36/0.61           = (k4_xboole_0 @ sk_A @ 
% 0.36/0.61              (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C_1))))),
% 0.36/0.61      inference('sup+', [status(thm)], ['11', '16'])).
% 0.36/0.61  thf('18', plain,
% 0.36/0.61      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1)) = (sk_A))),
% 0.36/0.61      inference('sup-', [status(thm)], ['12', '13'])).
% 0.36/0.61  thf('19', plain,
% 0.36/0.61      (![X0 : $i]:
% 0.36/0.61         ((sk_A)
% 0.36/0.61           = (k4_xboole_0 @ sk_A @ 
% 0.36/0.61              (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C_1))))),
% 0.36/0.61      inference('demod', [status(thm)], ['17', '18'])).
% 0.36/0.61  thf('20', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.36/0.61      inference('sup+', [status(thm)], ['10', '19'])).
% 0.36/0.61  thf('21', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]:
% 0.36/0.61         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.36/0.61      inference('demod', [status(thm)], ['4', '5'])).
% 0.36/0.61  thf(commutativity_k3_xboole_0, axiom,
% 0.36/0.61    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.36/0.61  thf('22', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.36/0.61  thf(d7_xboole_0, axiom,
% 0.36/0.61    (![A:$i,B:$i]:
% 0.36/0.61     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.36/0.61       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.36/0.61  thf('23', plain,
% 0.36/0.61      (![X4 : $i, X6 : $i]:
% 0.36/0.61         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 0.36/0.61      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.36/0.61  thf('24', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]:
% 0.36/0.61         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 0.36/0.61      inference('sup-', [status(thm)], ['22', '23'])).
% 0.36/0.61  thf('25', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]:
% 0.36/0.61         (((k1_xboole_0) != (k1_xboole_0))
% 0.36/0.61          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.36/0.61      inference('sup-', [status(thm)], ['21', '24'])).
% 0.36/0.61  thf('26', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.36/0.61      inference('simplify', [status(thm)], ['25'])).
% 0.36/0.61  thf('27', plain, ((r1_xboole_0 @ sk_A @ sk_C_1)),
% 0.36/0.61      inference('sup+', [status(thm)], ['20', '26'])).
% 0.36/0.61  thf('28', plain,
% 0.36/0.61      ((~ (r1_xboole_0 @ sk_A @ sk_C_1)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 0.36/0.61      inference('split', [status(esa)], ['0'])).
% 0.36/0.61  thf('29', plain, (((r1_xboole_0 @ sk_A @ sk_C_1))),
% 0.36/0.61      inference('sup-', [status(thm)], ['27', '28'])).
% 0.36/0.61  thf('30', plain,
% 0.36/0.61      (~ ((r1_tarski @ sk_A @ sk_B)) | ~ ((r1_xboole_0 @ sk_A @ sk_C_1))),
% 0.36/0.61      inference('split', [status(esa)], ['0'])).
% 0.36/0.61  thf('31', plain, (~ ((r1_tarski @ sk_A @ sk_B))),
% 0.36/0.61      inference('sat_resolution*', [status(thm)], ['29', '30'])).
% 0.36/0.61  thf('32', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.36/0.61      inference('simpl_trail', [status(thm)], ['1', '31'])).
% 0.36/0.61  thf(t21_xboole_1, axiom,
% 0.36/0.61    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.36/0.61  thf('33', plain,
% 0.36/0.61      (![X18 : $i, X19 : $i]:
% 0.36/0.61         ((k3_xboole_0 @ X18 @ (k2_xboole_0 @ X18 @ X19)) = (X18))),
% 0.36/0.61      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.36/0.61  thf('34', plain,
% 0.36/0.61      (![X16 : $i, X17 : $i]: (r1_tarski @ (k3_xboole_0 @ X16 @ X17) @ X16)),
% 0.36/0.61      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.36/0.61  thf('35', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.36/0.61      inference('sup+', [status(thm)], ['33', '34'])).
% 0.36/0.61  thf('36', plain,
% 0.36/0.61      (![X20 : $i, X21 : $i]:
% 0.36/0.61         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 0.36/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.36/0.61  thf('37', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.36/0.61      inference('sup-', [status(thm)], ['35', '36'])).
% 0.36/0.61  thf('38', plain,
% 0.36/0.61      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.36/0.61         ((k3_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X24))
% 0.36/0.61           = (k4_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ X24))),
% 0.36/0.61      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.36/0.61  thf('39', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]:
% 0.36/0.61         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.36/0.61           = (k4_xboole_0 @ X0 @ X1))),
% 0.36/0.61      inference('sup+', [status(thm)], ['37', '38'])).
% 0.36/0.61  thf('40', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.36/0.61  thf('41', plain,
% 0.36/0.61      (![X14 : $i, X15 : $i]:
% 0.36/0.61         ((k4_xboole_0 @ X14 @ X15)
% 0.36/0.61           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.36/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.36/0.61  thf('42', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]:
% 0.36/0.61         ((k4_xboole_0 @ X0 @ X1)
% 0.36/0.61           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.36/0.61      inference('sup+', [status(thm)], ['40', '41'])).
% 0.36/0.61  thf('43', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]:
% 0.36/0.61         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 0.36/0.61           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.36/0.61      inference('sup+', [status(thm)], ['39', '42'])).
% 0.36/0.61  thf(t92_xboole_1, axiom,
% 0.36/0.61    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.36/0.61  thf('44', plain, (![X29 : $i]: ((k5_xboole_0 @ X29 @ X29) = (k1_xboole_0))),
% 0.36/0.61      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.36/0.61  thf('45', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]:
% 0.36/0.61         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 0.36/0.61      inference('demod', [status(thm)], ['43', '44'])).
% 0.36/0.61  thf('46', plain,
% 0.36/0.61      (![X0 : $i]:
% 0.36/0.61         ((k3_xboole_0 @ sk_A @ 
% 0.36/0.61           (k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C_1) @ X0))
% 0.36/0.61           = (k4_xboole_0 @ sk_A @ X0))),
% 0.36/0.61      inference('sup+', [status(thm)], ['14', '15'])).
% 0.36/0.61  thf('47', plain,
% 0.36/0.61      (((k3_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.36/0.61      inference('sup+', [status(thm)], ['45', '46'])).
% 0.36/0.61  thf('48', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.36/0.61  thf('49', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.36/0.61  thf('50', plain,
% 0.36/0.61      (![X16 : $i, X17 : $i]: (r1_tarski @ (k3_xboole_0 @ X16 @ X17) @ X16)),
% 0.36/0.61      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.36/0.61  thf('51', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.36/0.61      inference('sup+', [status(thm)], ['49', '50'])).
% 0.36/0.61  thf('52', plain,
% 0.36/0.61      (![X11 : $i, X13 : $i]:
% 0.36/0.61         (((k4_xboole_0 @ X11 @ X13) = (k1_xboole_0))
% 0.36/0.61          | ~ (r1_tarski @ X11 @ X13))),
% 0.36/0.61      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.36/0.61  thf('53', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]:
% 0.36/0.61         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.36/0.61      inference('sup-', [status(thm)], ['51', '52'])).
% 0.36/0.61  thf('54', plain,
% 0.36/0.61      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.36/0.61         ((k3_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X24))
% 0.36/0.61           = (k4_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ X24))),
% 0.36/0.61      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.36/0.61  thf('55', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.36/0.61      inference('sup+', [status(thm)], ['33', '34'])).
% 0.36/0.61  thf('56', plain,
% 0.36/0.61      (![X11 : $i, X13 : $i]:
% 0.36/0.61         (((k4_xboole_0 @ X11 @ X13) = (k1_xboole_0))
% 0.36/0.61          | ~ (r1_tarski @ X11 @ X13))),
% 0.36/0.61      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.36/0.61  thf('57', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.36/0.61      inference('sup-', [status(thm)], ['55', '56'])).
% 0.36/0.61  thf('58', plain,
% 0.36/0.61      (![X1 : $i]: ((k3_xboole_0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.61      inference('demod', [status(thm)], ['53', '54', '57'])).
% 0.36/0.61  thf('59', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.36/0.61  thf('60', plain,
% 0.36/0.61      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.36/0.61      inference('sup+', [status(thm)], ['58', '59'])).
% 0.36/0.61  thf('61', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.36/0.61      inference('demod', [status(thm)], ['47', '48', '60'])).
% 0.36/0.61  thf('62', plain,
% 0.36/0.61      (![X11 : $i, X12 : $i]:
% 0.36/0.61         ((r1_tarski @ X11 @ X12)
% 0.36/0.61          | ((k4_xboole_0 @ X11 @ X12) != (k1_xboole_0)))),
% 0.36/0.61      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.36/0.61  thf('63', plain,
% 0.36/0.61      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 0.36/0.61      inference('sup-', [status(thm)], ['61', '62'])).
% 0.36/0.61  thf('64', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.36/0.61      inference('simplify', [status(thm)], ['63'])).
% 0.36/0.61  thf('65', plain, ($false), inference('demod', [status(thm)], ['32', '64'])).
% 0.36/0.61  
% 0.36/0.61  % SZS output end Refutation
% 0.36/0.61  
% 0.36/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
