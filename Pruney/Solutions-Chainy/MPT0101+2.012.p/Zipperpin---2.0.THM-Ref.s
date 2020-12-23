%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SLwPbVEGh2

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:56 EST 2020

% Result     : Theorem 17.07s
% Output     : Refutation 17.07s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 110 expanded)
%              Number of leaves         :   18 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :  579 ( 943 expanded)
%              Number of equality atoms :   57 (  92 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t94_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ A @ B )
        = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t94_xboole_1])).

thf('0',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('11',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k4_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('31',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k2_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('35',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('36',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k2_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k2_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','42'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('44',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['27','28','29','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('49',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['6','47','48'])).

thf('50',plain,(
    $false ),
    inference(simplify,[status(thm)],['49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SLwPbVEGh2
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:32:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 17.07/17.33  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 17.07/17.33  % Solved by: fo/fo7.sh
% 17.07/17.33  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 17.07/17.33  % done 5443 iterations in 16.853s
% 17.07/17.33  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 17.07/17.33  % SZS output start Refutation
% 17.07/17.33  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 17.07/17.33  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 17.07/17.33  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 17.07/17.33  thf(sk_A_type, type, sk_A: $i).
% 17.07/17.33  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 17.07/17.33  thf(sk_B_type, type, sk_B: $i).
% 17.07/17.33  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 17.07/17.33  thf(t94_xboole_1, conjecture,
% 17.07/17.33    (![A:$i,B:$i]:
% 17.07/17.33     ( ( k2_xboole_0 @ A @ B ) =
% 17.07/17.33       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 17.07/17.33  thf(zf_stmt_0, negated_conjecture,
% 17.07/17.33    (~( ![A:$i,B:$i]:
% 17.07/17.33        ( ( k2_xboole_0 @ A @ B ) =
% 17.07/17.33          ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 17.07/17.33    inference('cnf.neg', [status(esa)], [t94_xboole_1])).
% 17.07/17.33  thf('0', plain,
% 17.07/17.33      (((k2_xboole_0 @ sk_A @ sk_B)
% 17.07/17.33         != (k5_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ 
% 17.07/17.33             (k3_xboole_0 @ sk_A @ sk_B)))),
% 17.07/17.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.07/17.33  thf(d6_xboole_0, axiom,
% 17.07/17.33    (![A:$i,B:$i]:
% 17.07/17.33     ( ( k5_xboole_0 @ A @ B ) =
% 17.07/17.33       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 17.07/17.33  thf('1', plain,
% 17.07/17.33      (![X2 : $i, X3 : $i]:
% 17.07/17.33         ((k5_xboole_0 @ X2 @ X3)
% 17.07/17.33           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 17.07/17.33      inference('cnf', [status(esa)], [d6_xboole_0])).
% 17.07/17.33  thf(commutativity_k2_xboole_0, axiom,
% 17.07/17.33    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 17.07/17.33  thf('2', plain,
% 17.07/17.33      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 17.07/17.33      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 17.07/17.33  thf('3', plain,
% 17.07/17.33      (![X0 : $i, X1 : $i]:
% 17.07/17.33         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 17.07/17.33           = (k5_xboole_0 @ X1 @ X0))),
% 17.07/17.33      inference('sup+', [status(thm)], ['1', '2'])).
% 17.07/17.33  thf('4', plain,
% 17.07/17.33      (![X2 : $i, X3 : $i]:
% 17.07/17.33         ((k5_xboole_0 @ X2 @ X3)
% 17.07/17.33           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 17.07/17.33      inference('cnf', [status(esa)], [d6_xboole_0])).
% 17.07/17.33  thf('5', plain,
% 17.07/17.33      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 17.07/17.33      inference('sup+', [status(thm)], ['3', '4'])).
% 17.07/17.33  thf('6', plain,
% 17.07/17.33      (((k2_xboole_0 @ sk_A @ sk_B)
% 17.07/17.33         != (k5_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 17.07/17.33             (k5_xboole_0 @ sk_A @ sk_B)))),
% 17.07/17.33      inference('demod', [status(thm)], ['0', '5'])).
% 17.07/17.33  thf('7', plain,
% 17.07/17.33      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 17.07/17.33      inference('sup+', [status(thm)], ['3', '4'])).
% 17.07/17.33  thf(t79_xboole_1, axiom,
% 17.07/17.33    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 17.07/17.33  thf('8', plain,
% 17.07/17.33      (![X17 : $i, X18 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X18)),
% 17.07/17.33      inference('cnf', [status(esa)], [t79_xboole_1])).
% 17.07/17.33  thf(symmetry_r1_xboole_0, axiom,
% 17.07/17.33    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 17.07/17.33  thf('9', plain,
% 17.07/17.33      (![X5 : $i, X6 : $i]:
% 17.07/17.33         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 17.07/17.33      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 17.07/17.33  thf('10', plain,
% 17.07/17.33      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 17.07/17.33      inference('sup-', [status(thm)], ['8', '9'])).
% 17.07/17.33  thf(t83_xboole_1, axiom,
% 17.07/17.33    (![A:$i,B:$i]:
% 17.07/17.33     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 17.07/17.33  thf('11', plain,
% 17.07/17.33      (![X19 : $i, X20 : $i]:
% 17.07/17.33         (((k4_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_xboole_0 @ X19 @ X20))),
% 17.07/17.33      inference('cnf', [status(esa)], [t83_xboole_1])).
% 17.07/17.33  thf('12', plain,
% 17.07/17.33      (![X0 : $i, X1 : $i]:
% 17.07/17.33         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 17.07/17.33      inference('sup-', [status(thm)], ['10', '11'])).
% 17.07/17.33  thf('13', plain,
% 17.07/17.33      (![X2 : $i, X3 : $i]:
% 17.07/17.33         ((k5_xboole_0 @ X2 @ X3)
% 17.07/17.33           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 17.07/17.33      inference('cnf', [status(esa)], [d6_xboole_0])).
% 17.07/17.33  thf(t41_xboole_1, axiom,
% 17.07/17.33    (![A:$i,B:$i,C:$i]:
% 17.07/17.33     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 17.07/17.33       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 17.07/17.33  thf('14', plain,
% 17.07/17.33      (![X9 : $i, X10 : $i, X11 : $i]:
% 17.07/17.33         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 17.07/17.33           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 17.07/17.33      inference('cnf', [status(esa)], [t41_xboole_1])).
% 17.07/17.33  thf('15', plain,
% 17.07/17.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.07/17.33         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 17.07/17.33           (k4_xboole_0 @ X0 @ X1))
% 17.07/17.33           = (k4_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 17.07/17.33      inference('sup+', [status(thm)], ['13', '14'])).
% 17.07/17.33  thf('16', plain,
% 17.07/17.33      (![X0 : $i, X1 : $i]:
% 17.07/17.33         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 17.07/17.33           = (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 17.07/17.33      inference('sup+', [status(thm)], ['12', '15'])).
% 17.07/17.33  thf(t48_xboole_1, axiom,
% 17.07/17.33    (![A:$i,B:$i]:
% 17.07/17.33     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 17.07/17.33  thf('17', plain,
% 17.07/17.33      (![X12 : $i, X13 : $i]:
% 17.07/17.33         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 17.07/17.33           = (k3_xboole_0 @ X12 @ X13))),
% 17.07/17.33      inference('cnf', [status(esa)], [t48_xboole_1])).
% 17.07/17.33  thf('18', plain,
% 17.07/17.33      (![X0 : $i, X1 : $i]:
% 17.07/17.33         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 17.07/17.33           = (k3_xboole_0 @ X0 @ X1))),
% 17.07/17.33      inference('sup+', [status(thm)], ['16', '17'])).
% 17.07/17.33  thf('19', plain,
% 17.07/17.33      (![X0 : $i, X1 : $i]:
% 17.07/17.33         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))
% 17.07/17.33           = (k3_xboole_0 @ X1 @ X0))),
% 17.07/17.33      inference('sup+', [status(thm)], ['7', '18'])).
% 17.07/17.33  thf('20', plain,
% 17.07/17.33      (![X0 : $i, X1 : $i]:
% 17.07/17.33         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 17.07/17.33      inference('sup-', [status(thm)], ['10', '11'])).
% 17.07/17.33  thf('21', plain,
% 17.07/17.33      (![X2 : $i, X3 : $i]:
% 17.07/17.33         ((k5_xboole_0 @ X2 @ X3)
% 17.07/17.33           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 17.07/17.33      inference('cnf', [status(esa)], [d6_xboole_0])).
% 17.07/17.33  thf('22', plain,
% 17.07/17.33      (![X0 : $i, X1 : $i]:
% 17.07/17.33         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 17.07/17.33           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)))),
% 17.07/17.33      inference('sup+', [status(thm)], ['20', '21'])).
% 17.07/17.33  thf(t39_xboole_1, axiom,
% 17.07/17.33    (![A:$i,B:$i]:
% 17.07/17.33     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 17.07/17.33  thf('23', plain,
% 17.07/17.33      (![X7 : $i, X8 : $i]:
% 17.07/17.33         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 17.07/17.33           = (k2_xboole_0 @ X7 @ X8))),
% 17.07/17.33      inference('cnf', [status(esa)], [t39_xboole_1])).
% 17.07/17.33  thf('24', plain,
% 17.07/17.33      (![X0 : $i, X1 : $i]:
% 17.07/17.33         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 17.07/17.33           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 17.07/17.33      inference('demod', [status(thm)], ['22', '23'])).
% 17.07/17.33  thf('25', plain,
% 17.07/17.33      (![X7 : $i, X8 : $i]:
% 17.07/17.33         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 17.07/17.33           = (k2_xboole_0 @ X7 @ X8))),
% 17.07/17.33      inference('cnf', [status(esa)], [t39_xboole_1])).
% 17.07/17.33  thf('26', plain,
% 17.07/17.33      (![X0 : $i, X1 : $i]:
% 17.07/17.33         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 17.07/17.33           = (k2_xboole_0 @ X0 @ X1))),
% 17.07/17.33      inference('sup+', [status(thm)], ['24', '25'])).
% 17.07/17.33  thf('27', plain,
% 17.07/17.33      (![X0 : $i, X1 : $i]:
% 17.07/17.33         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 17.07/17.33           = (k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X1))),
% 17.07/17.33      inference('sup+', [status(thm)], ['19', '26'])).
% 17.07/17.33  thf('28', plain,
% 17.07/17.33      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 17.07/17.33      inference('sup+', [status(thm)], ['3', '4'])).
% 17.07/17.33  thf('29', plain,
% 17.07/17.33      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 17.07/17.33      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 17.07/17.33  thf('30', plain,
% 17.07/17.33      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 17.07/17.33      inference('sup+', [status(thm)], ['3', '4'])).
% 17.07/17.33  thf(t4_xboole_1, axiom,
% 17.07/17.33    (![A:$i,B:$i,C:$i]:
% 17.07/17.33     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 17.07/17.33       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 17.07/17.33  thf('31', plain,
% 17.07/17.33      (![X14 : $i, X15 : $i, X16 : $i]:
% 17.07/17.33         ((k2_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ X16)
% 17.07/17.33           = (k2_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 17.07/17.33      inference('cnf', [status(esa)], [t4_xboole_1])).
% 17.07/17.33  thf('32', plain,
% 17.07/17.33      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 17.07/17.33      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 17.07/17.33  thf('33', plain,
% 17.07/17.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.07/17.33         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1))
% 17.07/17.33           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 17.07/17.33      inference('sup+', [status(thm)], ['31', '32'])).
% 17.07/17.33  thf('34', plain,
% 17.07/17.33      (![X2 : $i, X3 : $i]:
% 17.07/17.33         ((k5_xboole_0 @ X2 @ X3)
% 17.07/17.33           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 17.07/17.33      inference('cnf', [status(esa)], [d6_xboole_0])).
% 17.07/17.33  thf('35', plain,
% 17.07/17.33      (![X7 : $i, X8 : $i]:
% 17.07/17.33         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 17.07/17.33           = (k2_xboole_0 @ X7 @ X8))),
% 17.07/17.33      inference('cnf', [status(esa)], [t39_xboole_1])).
% 17.07/17.33  thf('36', plain,
% 17.07/17.33      (![X14 : $i, X15 : $i, X16 : $i]:
% 17.07/17.33         ((k2_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ X16)
% 17.07/17.33           = (k2_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 17.07/17.33      inference('cnf', [status(esa)], [t4_xboole_1])).
% 17.07/17.33  thf('37', plain,
% 17.07/17.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.07/17.33         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 17.07/17.33           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)))),
% 17.07/17.33      inference('sup+', [status(thm)], ['35', '36'])).
% 17.07/17.33  thf('38', plain,
% 17.07/17.33      (![X14 : $i, X15 : $i, X16 : $i]:
% 17.07/17.33         ((k2_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ X16)
% 17.07/17.33           = (k2_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 17.07/17.33      inference('cnf', [status(esa)], [t4_xboole_1])).
% 17.07/17.33  thf('39', plain,
% 17.07/17.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.07/17.33         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2))
% 17.07/17.33           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)))),
% 17.07/17.33      inference('demod', [status(thm)], ['37', '38'])).
% 17.07/17.33  thf('40', plain,
% 17.07/17.33      (![X0 : $i, X1 : $i]:
% 17.07/17.33         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))
% 17.07/17.33           = (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 17.07/17.33      inference('sup+', [status(thm)], ['34', '39'])).
% 17.07/17.33  thf('41', plain,
% 17.07/17.33      (![X7 : $i, X8 : $i]:
% 17.07/17.33         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 17.07/17.33           = (k2_xboole_0 @ X7 @ X8))),
% 17.07/17.33      inference('cnf', [status(esa)], [t39_xboole_1])).
% 17.07/17.33  thf('42', plain,
% 17.07/17.33      (![X0 : $i, X1 : $i]:
% 17.07/17.33         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 17.07/17.33           = (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 17.07/17.33      inference('demod', [status(thm)], ['40', '41'])).
% 17.07/17.33  thf('43', plain,
% 17.07/17.33      (![X0 : $i, X1 : $i]:
% 17.07/17.33         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X0))
% 17.07/17.33           = (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 17.07/17.33      inference('sup+', [status(thm)], ['33', '42'])).
% 17.07/17.33  thf(idempotence_k2_xboole_0, axiom,
% 17.07/17.33    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 17.07/17.33  thf('44', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ X4) = (X4))),
% 17.07/17.33      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 17.07/17.33  thf('45', plain,
% 17.07/17.33      (![X0 : $i, X1 : $i]:
% 17.07/17.33         ((k2_xboole_0 @ X1 @ X0)
% 17.07/17.33           = (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 17.07/17.33      inference('demod', [status(thm)], ['43', '44'])).
% 17.07/17.33  thf('46', plain,
% 17.07/17.33      (![X0 : $i, X1 : $i]:
% 17.07/17.33         ((k2_xboole_0 @ X0 @ X1)
% 17.07/17.33           = (k2_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 17.07/17.33      inference('sup+', [status(thm)], ['30', '45'])).
% 17.07/17.33  thf('47', plain,
% 17.07/17.33      (![X0 : $i, X1 : $i]:
% 17.07/17.33         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 17.07/17.33           = (k2_xboole_0 @ X0 @ X1))),
% 17.07/17.33      inference('demod', [status(thm)], ['27', '28', '29', '46'])).
% 17.07/17.33  thf('48', plain,
% 17.07/17.33      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 17.07/17.33      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 17.07/17.33  thf('49', plain,
% 17.07/17.33      (((k2_xboole_0 @ sk_A @ sk_B) != (k2_xboole_0 @ sk_A @ sk_B))),
% 17.07/17.33      inference('demod', [status(thm)], ['6', '47', '48'])).
% 17.07/17.33  thf('50', plain, ($false), inference('simplify', [status(thm)], ['49'])).
% 17.07/17.33  
% 17.07/17.33  % SZS output end Refutation
% 17.07/17.33  
% 17.07/17.34  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
