%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jDyVTtBp7H

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:31 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 140 expanded)
%              Number of leaves         :   24 (  50 expanded)
%              Depth                    :   13
%              Number of atoms          :  539 ( 936 expanded)
%              Number of equality atoms :   53 (  83 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X24: $i,X25: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X24 @ X25 ) @ X25 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('3',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('4',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X21 @ X22 )
      | ~ ( r1_xboole_0 @ X22 @ X23 )
      | ( r1_xboole_0 @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('8',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','10'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('17',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('18',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('19',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('20',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ ( k3_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('23',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['21','26'])).

thf('28',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['14','27'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('29',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('30',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('33',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k4_xboole_0 @ X26 @ X27 )
        = X26 )
      | ~ ( r1_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('36',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['28','34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('38',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X24 @ X25 ) @ X25 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('42',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('48',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['21','26'])).

thf('51',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('53',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_A )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('55',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( k1_xboole_0
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['53','58'])).

thf('60',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['40','59'])).

thf('61',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('62',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    $false ),
    inference(demod,[status(thm)],['11','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jDyVTtBp7H
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:53:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.36/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.52  % Solved by: fo/fo7.sh
% 0.36/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.52  % done 218 iterations in 0.075s
% 0.36/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.52  % SZS output start Refutation
% 0.36/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.36/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.52  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.36/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.52  thf(t106_xboole_1, conjecture,
% 0.36/0.52    (![A:$i,B:$i,C:$i]:
% 0.36/0.52     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.36/0.52       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.36/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.36/0.52        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.36/0.52          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 0.36/0.52    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 0.36/0.52  thf('0', plain,
% 0.36/0.52      ((~ (r1_tarski @ sk_A @ sk_B) | ~ (r1_xboole_0 @ sk_A @ sk_C))),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf('1', plain,
% 0.36/0.52      ((~ (r1_tarski @ sk_A @ sk_B)) <= (~ ((r1_tarski @ sk_A @ sk_B)))),
% 0.36/0.52      inference('split', [status(esa)], ['0'])).
% 0.36/0.52  thf(t79_xboole_1, axiom,
% 0.36/0.52    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.36/0.52  thf('2', plain,
% 0.36/0.52      (![X24 : $i, X25 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X24 @ X25) @ X25)),
% 0.36/0.52      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.36/0.52  thf('3', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf(t63_xboole_1, axiom,
% 0.36/0.52    (![A:$i,B:$i,C:$i]:
% 0.36/0.52     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.36/0.52       ( r1_xboole_0 @ A @ C ) ))).
% 0.36/0.52  thf('4', plain,
% 0.36/0.52      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.36/0.52         (~ (r1_tarski @ X21 @ X22)
% 0.36/0.52          | ~ (r1_xboole_0 @ X22 @ X23)
% 0.36/0.52          | (r1_xboole_0 @ X21 @ X23))),
% 0.36/0.52      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.36/0.52  thf('5', plain,
% 0.36/0.52      (![X0 : $i]:
% 0.36/0.52         ((r1_xboole_0 @ sk_A @ X0)
% 0.36/0.52          | ~ (r1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ X0))),
% 0.36/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.36/0.52  thf('6', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.36/0.52      inference('sup-', [status(thm)], ['2', '5'])).
% 0.36/0.52  thf('7', plain,
% 0.36/0.52      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.36/0.52      inference('split', [status(esa)], ['0'])).
% 0.36/0.52  thf('8', plain, (((r1_xboole_0 @ sk_A @ sk_C))),
% 0.36/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.36/0.52  thf('9', plain,
% 0.36/0.52      (~ ((r1_tarski @ sk_A @ sk_B)) | ~ ((r1_xboole_0 @ sk_A @ sk_C))),
% 0.36/0.52      inference('split', [status(esa)], ['0'])).
% 0.36/0.52  thf('10', plain, (~ ((r1_tarski @ sk_A @ sk_B))),
% 0.36/0.52      inference('sat_resolution*', [status(thm)], ['8', '9'])).
% 0.36/0.52  thf('11', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.36/0.52      inference('simpl_trail', [status(thm)], ['1', '10'])).
% 0.36/0.52  thf(t36_xboole_1, axiom,
% 0.36/0.52    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.36/0.52  thf('12', plain,
% 0.36/0.52      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 0.36/0.52      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.36/0.52  thf(l32_xboole_1, axiom,
% 0.36/0.52    (![A:$i,B:$i]:
% 0.36/0.52     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.52  thf('13', plain,
% 0.36/0.52      (![X5 : $i, X7 : $i]:
% 0.36/0.52         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.36/0.52      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.36/0.52  thf('14', plain,
% 0.36/0.52      (![X0 : $i, X1 : $i]:
% 0.36/0.52         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.36/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.36/0.52  thf('15', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf(t12_xboole_1, axiom,
% 0.36/0.52    (![A:$i,B:$i]:
% 0.36/0.52     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.36/0.52  thf('16', plain,
% 0.36/0.52      (![X10 : $i, X11 : $i]:
% 0.36/0.52         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.36/0.52      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.36/0.52  thf('17', plain,
% 0.36/0.52      (((k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))
% 0.36/0.52         = (k4_xboole_0 @ sk_B @ sk_C))),
% 0.36/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.36/0.52  thf(t46_xboole_1, axiom,
% 0.36/0.52    (![A:$i,B:$i]:
% 0.36/0.52     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.36/0.52  thf('18', plain,
% 0.36/0.52      (![X15 : $i, X16 : $i]:
% 0.36/0.52         ((k4_xboole_0 @ X15 @ (k2_xboole_0 @ X15 @ X16)) = (k1_xboole_0))),
% 0.36/0.52      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.36/0.52  thf('19', plain,
% 0.36/0.52      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 0.36/0.52      inference('sup+', [status(thm)], ['17', '18'])).
% 0.36/0.52  thf(t52_xboole_1, axiom,
% 0.36/0.52    (![A:$i,B:$i,C:$i]:
% 0.36/0.52     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.36/0.52       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.36/0.52  thf('20', plain,
% 0.36/0.52      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.36/0.52         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X19))
% 0.36/0.52           = (k2_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ 
% 0.36/0.52              (k3_xboole_0 @ X17 @ X19)))),
% 0.36/0.52      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.36/0.52  thf('21', plain,
% 0.36/0.52      (![X0 : $i]:
% 0.36/0.52         ((k4_xboole_0 @ sk_A @ 
% 0.36/0.52           (k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ X0))
% 0.36/0.52           = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0)))),
% 0.36/0.52      inference('sup+', [status(thm)], ['19', '20'])).
% 0.36/0.52  thf('22', plain,
% 0.36/0.52      (![X15 : $i, X16 : $i]:
% 0.36/0.52         ((k4_xboole_0 @ X15 @ (k2_xboole_0 @ X15 @ X16)) = (k1_xboole_0))),
% 0.36/0.52      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.36/0.52  thf('23', plain,
% 0.36/0.52      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 0.36/0.52      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.36/0.52  thf('24', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.36/0.52      inference('sup+', [status(thm)], ['22', '23'])).
% 0.36/0.52  thf('25', plain,
% 0.36/0.52      (![X10 : $i, X11 : $i]:
% 0.36/0.52         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.36/0.52      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.36/0.52  thf('26', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.36/0.52      inference('sup-', [status(thm)], ['24', '25'])).
% 0.36/0.52  thf('27', plain,
% 0.36/0.52      (![X0 : $i]:
% 0.36/0.52         ((k4_xboole_0 @ sk_A @ 
% 0.36/0.52           (k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ X0))
% 0.36/0.52           = (k3_xboole_0 @ sk_A @ X0))),
% 0.36/0.52      inference('demod', [status(thm)], ['21', '26'])).
% 0.36/0.52  thf('28', plain,
% 0.36/0.52      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.36/0.52      inference('sup+', [status(thm)], ['14', '27'])).
% 0.36/0.52  thf(t2_boole, axiom,
% 0.36/0.52    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.36/0.52  thf('29', plain,
% 0.36/0.52      (![X12 : $i]: ((k3_xboole_0 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.52      inference('cnf', [status(esa)], [t2_boole])).
% 0.36/0.52  thf(d7_xboole_0, axiom,
% 0.36/0.52    (![A:$i,B:$i]:
% 0.36/0.52     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.36/0.52       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.36/0.52  thf('30', plain,
% 0.36/0.52      (![X2 : $i, X4 : $i]:
% 0.36/0.52         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.36/0.52      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.36/0.52  thf('31', plain,
% 0.36/0.52      (![X0 : $i]:
% 0.36/0.52         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.36/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.36/0.52  thf('32', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.36/0.52      inference('simplify', [status(thm)], ['31'])).
% 0.36/0.52  thf(t83_xboole_1, axiom,
% 0.36/0.52    (![A:$i,B:$i]:
% 0.36/0.52     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.36/0.52  thf('33', plain,
% 0.36/0.52      (![X26 : $i, X27 : $i]:
% 0.36/0.52         (((k4_xboole_0 @ X26 @ X27) = (X26)) | ~ (r1_xboole_0 @ X26 @ X27))),
% 0.36/0.52      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.36/0.52  thf('34', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.36/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.36/0.52  thf(commutativity_k3_xboole_0, axiom,
% 0.36/0.52    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.36/0.52  thf('35', plain,
% 0.36/0.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.52      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.36/0.52  thf('36', plain, (((sk_A) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.36/0.52      inference('demod', [status(thm)], ['28', '34', '35'])).
% 0.36/0.52  thf('37', plain,
% 0.36/0.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.52      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.36/0.52  thf(t100_xboole_1, axiom,
% 0.36/0.52    (![A:$i,B:$i]:
% 0.36/0.52     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.36/0.52  thf('38', plain,
% 0.36/0.52      (![X8 : $i, X9 : $i]:
% 0.36/0.52         ((k4_xboole_0 @ X8 @ X9)
% 0.36/0.52           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.36/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.36/0.52  thf('39', plain,
% 0.36/0.52      (![X0 : $i, X1 : $i]:
% 0.36/0.52         ((k4_xboole_0 @ X0 @ X1)
% 0.36/0.52           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.36/0.52      inference('sup+', [status(thm)], ['37', '38'])).
% 0.36/0.52  thf('40', plain,
% 0.36/0.52      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.36/0.52      inference('sup+', [status(thm)], ['36', '39'])).
% 0.36/0.52  thf('41', plain,
% 0.36/0.52      (![X24 : $i, X25 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X24 @ X25) @ X25)),
% 0.36/0.52      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.36/0.52  thf('42', plain,
% 0.36/0.52      (![X2 : $i, X3 : $i]:
% 0.36/0.52         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.36/0.52      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.36/0.52  thf('43', plain,
% 0.36/0.52      (![X0 : $i, X1 : $i]:
% 0.36/0.52         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.36/0.52      inference('sup-', [status(thm)], ['41', '42'])).
% 0.36/0.52  thf('44', plain,
% 0.36/0.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.52      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.36/0.52  thf('45', plain,
% 0.36/0.52      (![X0 : $i, X1 : $i]:
% 0.36/0.52         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.36/0.52      inference('demod', [status(thm)], ['43', '44'])).
% 0.36/0.52  thf('46', plain,
% 0.36/0.52      (![X8 : $i, X9 : $i]:
% 0.36/0.52         ((k4_xboole_0 @ X8 @ X9)
% 0.36/0.52           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.36/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.36/0.52  thf('47', plain,
% 0.36/0.52      (![X0 : $i, X1 : $i]:
% 0.36/0.52         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.36/0.52           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.36/0.52      inference('sup+', [status(thm)], ['45', '46'])).
% 0.36/0.52  thf(t5_boole, axiom,
% 0.36/0.52    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.36/0.52  thf('48', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.36/0.52      inference('cnf', [status(esa)], [t5_boole])).
% 0.36/0.52  thf('49', plain,
% 0.36/0.52      (![X0 : $i, X1 : $i]:
% 0.36/0.52         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.36/0.52      inference('demod', [status(thm)], ['47', '48'])).
% 0.36/0.52  thf('50', plain,
% 0.36/0.52      (![X0 : $i]:
% 0.36/0.52         ((k4_xboole_0 @ sk_A @ 
% 0.36/0.52           (k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ X0))
% 0.36/0.52           = (k3_xboole_0 @ sk_A @ X0))),
% 0.36/0.52      inference('demod', [status(thm)], ['21', '26'])).
% 0.36/0.52  thf('51', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_A))),
% 0.36/0.52      inference('sup+', [status(thm)], ['49', '50'])).
% 0.36/0.52  thf('52', plain,
% 0.36/0.52      (![X8 : $i, X9 : $i]:
% 0.36/0.52         ((k4_xboole_0 @ X8 @ X9)
% 0.36/0.52           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.36/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.36/0.52  thf('53', plain,
% 0.36/0.52      (((k4_xboole_0 @ sk_A @ sk_A) = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.36/0.52      inference('sup+', [status(thm)], ['51', '52'])).
% 0.36/0.52  thf('54', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.36/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.36/0.52  thf('55', plain,
% 0.36/0.52      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 0.36/0.52      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.36/0.52  thf('56', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.36/0.52      inference('sup+', [status(thm)], ['54', '55'])).
% 0.36/0.52  thf('57', plain,
% 0.36/0.52      (![X5 : $i, X7 : $i]:
% 0.36/0.52         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.36/0.52      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.36/0.52  thf('58', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.36/0.52      inference('sup-', [status(thm)], ['56', '57'])).
% 0.36/0.52  thf('59', plain, (((k1_xboole_0) = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.36/0.52      inference('demod', [status(thm)], ['53', '58'])).
% 0.36/0.52  thf('60', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.36/0.52      inference('sup+', [status(thm)], ['40', '59'])).
% 0.36/0.52  thf('61', plain,
% 0.36/0.52      (![X5 : $i, X6 : $i]:
% 0.36/0.52         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 0.36/0.52      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.36/0.52  thf('62', plain,
% 0.36/0.52      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 0.36/0.52      inference('sup-', [status(thm)], ['60', '61'])).
% 0.36/0.52  thf('63', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.36/0.52      inference('simplify', [status(thm)], ['62'])).
% 0.36/0.52  thf('64', plain, ($false), inference('demod', [status(thm)], ['11', '63'])).
% 0.36/0.52  
% 0.36/0.52  % SZS output end Refutation
% 0.36/0.52  
% 0.38/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
