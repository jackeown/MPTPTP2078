%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.y4u5kRmvjL

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:17 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   77 (  91 expanded)
%              Number of leaves         :   25 (  38 expanded)
%              Depth                    :   13
%              Number of atoms          :  546 ( 682 expanded)
%              Number of equality atoms :   46 (  56 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t76_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_xboole_0 @ A @ B )
       => ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ ( k3_xboole_0 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('3',plain,(
    ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_C_1 ) @ ( k3_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('5',plain,(
    r1_xboole_0 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('6',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('15',plain,
    ( sk_B_1
    = ( k4_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('16',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X23 @ X24 ) @ ( k3_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k2_xboole_0 @ sk_B_1 @ ( k3_xboole_0 @ sk_B_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('18',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = sk_B_1 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B_1 @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = sk_B_1 ) ),
    inference('sup+',[status(thm)],['4','19'])).

thf('21',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B_1 @ sk_B_1 )
      = ( k3_xboole_0 @ sk_B_1 @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('24',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('26',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B_1 @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('30',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('31',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('32',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t50_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('36',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k3_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k3_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t50_xboole_1])).

thf('37',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('38',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k3_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ ( k3_xboole_0 @ X20 @ X22 ) ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['35','38','39'])).

thf('41',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['29','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X1 ) @ ( k3_xboole_0 @ sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','44'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('46',plain,(
    ! [X26: $i] :
      ( r1_xboole_0 @ X26 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('47',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X1 ) @ ( k3_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['3','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.y4u5kRmvjL
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:33:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.61/1.79  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.61/1.79  % Solved by: fo/fo7.sh
% 1.61/1.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.61/1.79  % done 2191 iterations in 1.329s
% 1.61/1.79  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.61/1.79  % SZS output start Refutation
% 1.61/1.79  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.61/1.79  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.61/1.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.61/1.79  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.61/1.79  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.61/1.79  thf(sk_B_type, type, sk_B: $i > $i).
% 1.61/1.79  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.61/1.79  thf(sk_A_type, type, sk_A: $i).
% 1.61/1.79  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.61/1.79  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.61/1.79  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.61/1.79  thf(t76_xboole_1, conjecture,
% 1.61/1.79    (![A:$i,B:$i,C:$i]:
% 1.61/1.79     ( ( r1_xboole_0 @ A @ B ) =>
% 1.61/1.79       ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ))).
% 1.61/1.79  thf(zf_stmt_0, negated_conjecture,
% 1.61/1.79    (~( ![A:$i,B:$i,C:$i]:
% 1.61/1.79        ( ( r1_xboole_0 @ A @ B ) =>
% 1.61/1.79          ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ) )),
% 1.61/1.79    inference('cnf.neg', [status(esa)], [t76_xboole_1])).
% 1.61/1.79  thf('0', plain,
% 1.61/1.79      (~ (r1_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ 
% 1.61/1.79          (k3_xboole_0 @ sk_C_1 @ sk_B_1))),
% 1.61/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.79  thf(commutativity_k3_xboole_0, axiom,
% 1.61/1.79    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.61/1.79  thf('1', plain,
% 1.61/1.79      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.61/1.79      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.61/1.79  thf('2', plain,
% 1.61/1.79      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.61/1.79      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.61/1.79  thf('3', plain,
% 1.61/1.79      (~ (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_C_1) @ 
% 1.61/1.79          (k3_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.61/1.79      inference('demod', [status(thm)], ['0', '1', '2'])).
% 1.61/1.79  thf(t48_xboole_1, axiom,
% 1.61/1.79    (![A:$i,B:$i]:
% 1.61/1.79     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.61/1.79  thf('4', plain,
% 1.61/1.79      (![X15 : $i, X16 : $i]:
% 1.61/1.79         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 1.61/1.79           = (k3_xboole_0 @ X15 @ X16))),
% 1.61/1.79      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.61/1.79  thf('5', plain, ((r1_xboole_0 @ sk_A @ sk_B_1)),
% 1.61/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.79  thf(t7_xboole_0, axiom,
% 1.61/1.79    (![A:$i]:
% 1.61/1.79     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.61/1.79          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 1.61/1.79  thf('6', plain,
% 1.61/1.79      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 1.61/1.79      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.61/1.79  thf(t4_xboole_0, axiom,
% 1.61/1.79    (![A:$i,B:$i]:
% 1.61/1.79     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.61/1.79            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.61/1.79       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.61/1.79            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.61/1.79  thf('7', plain,
% 1.61/1.79      (![X4 : $i, X6 : $i, X7 : $i]:
% 1.61/1.79         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 1.61/1.79          | ~ (r1_xboole_0 @ X4 @ X7))),
% 1.61/1.79      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.61/1.79  thf('8', plain,
% 1.61/1.79      (![X0 : $i, X1 : $i]:
% 1.61/1.79         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.61/1.79      inference('sup-', [status(thm)], ['6', '7'])).
% 1.61/1.79  thf('9', plain, (((k3_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 1.61/1.79      inference('sup-', [status(thm)], ['5', '8'])).
% 1.61/1.79  thf('10', plain,
% 1.61/1.79      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.61/1.79      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.61/1.79  thf(t47_xboole_1, axiom,
% 1.61/1.79    (![A:$i,B:$i]:
% 1.61/1.79     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.61/1.79  thf('11', plain,
% 1.61/1.79      (![X13 : $i, X14 : $i]:
% 1.61/1.79         ((k4_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14))
% 1.61/1.79           = (k4_xboole_0 @ X13 @ X14))),
% 1.61/1.79      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.61/1.79  thf('12', plain,
% 1.61/1.79      (![X0 : $i, X1 : $i]:
% 1.61/1.79         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.61/1.79           = (k4_xboole_0 @ X0 @ X1))),
% 1.61/1.79      inference('sup+', [status(thm)], ['10', '11'])).
% 1.61/1.79  thf('13', plain,
% 1.61/1.79      (((k4_xboole_0 @ sk_B_1 @ k1_xboole_0) = (k4_xboole_0 @ sk_B_1 @ sk_A))),
% 1.61/1.79      inference('sup+', [status(thm)], ['9', '12'])).
% 1.61/1.79  thf(t3_boole, axiom,
% 1.61/1.79    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.61/1.79  thf('14', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.61/1.79      inference('cnf', [status(esa)], [t3_boole])).
% 1.61/1.79  thf('15', plain, (((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ sk_A))),
% 1.61/1.79      inference('demod', [status(thm)], ['13', '14'])).
% 1.61/1.79  thf(t52_xboole_1, axiom,
% 1.61/1.79    (![A:$i,B:$i,C:$i]:
% 1.61/1.79     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 1.61/1.79       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 1.61/1.79  thf('16', plain,
% 1.61/1.79      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.61/1.79         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X25))
% 1.61/1.79           = (k2_xboole_0 @ (k4_xboole_0 @ X23 @ X24) @ 
% 1.61/1.79              (k3_xboole_0 @ X23 @ X25)))),
% 1.61/1.79      inference('cnf', [status(esa)], [t52_xboole_1])).
% 1.61/1.79  thf('17', plain,
% 1.61/1.79      (![X0 : $i]:
% 1.61/1.79         ((k4_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ sk_A @ X0))
% 1.61/1.79           = (k2_xboole_0 @ sk_B_1 @ (k3_xboole_0 @ sk_B_1 @ X0)))),
% 1.61/1.79      inference('sup+', [status(thm)], ['15', '16'])).
% 1.61/1.79  thf(t22_xboole_1, axiom,
% 1.61/1.79    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 1.61/1.79  thf('18', plain,
% 1.61/1.79      (![X9 : $i, X10 : $i]:
% 1.61/1.79         ((k2_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)) = (X9))),
% 1.61/1.79      inference('cnf', [status(esa)], [t22_xboole_1])).
% 1.61/1.79  thf('19', plain,
% 1.61/1.79      (![X0 : $i]:
% 1.61/1.79         ((k4_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ sk_A @ X0)) = (sk_B_1))),
% 1.61/1.79      inference('demod', [status(thm)], ['17', '18'])).
% 1.61/1.79  thf('20', plain,
% 1.61/1.79      (![X0 : $i]:
% 1.61/1.79         ((k4_xboole_0 @ sk_B_1 @ (k3_xboole_0 @ sk_A @ X0)) = (sk_B_1))),
% 1.61/1.79      inference('sup+', [status(thm)], ['4', '19'])).
% 1.61/1.79  thf('21', plain,
% 1.61/1.79      (![X15 : $i, X16 : $i]:
% 1.61/1.79         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 1.61/1.79           = (k3_xboole_0 @ X15 @ X16))),
% 1.61/1.79      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.61/1.79  thf('22', plain,
% 1.61/1.79      (![X0 : $i]:
% 1.61/1.79         ((k4_xboole_0 @ sk_B_1 @ sk_B_1)
% 1.61/1.79           = (k3_xboole_0 @ sk_B_1 @ (k3_xboole_0 @ sk_A @ X0)))),
% 1.61/1.79      inference('sup+', [status(thm)], ['20', '21'])).
% 1.61/1.79  thf('23', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.61/1.79      inference('cnf', [status(esa)], [t3_boole])).
% 1.61/1.79  thf('24', plain,
% 1.61/1.79      (![X15 : $i, X16 : $i]:
% 1.61/1.79         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 1.61/1.79           = (k3_xboole_0 @ X15 @ X16))),
% 1.61/1.79      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.61/1.79  thf('25', plain,
% 1.61/1.79      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.61/1.79      inference('sup+', [status(thm)], ['23', '24'])).
% 1.61/1.79  thf(t2_boole, axiom,
% 1.61/1.79    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.61/1.79  thf('26', plain,
% 1.61/1.79      (![X11 : $i]: ((k3_xboole_0 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 1.61/1.79      inference('cnf', [status(esa)], [t2_boole])).
% 1.61/1.79  thf('27', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.61/1.79      inference('demod', [status(thm)], ['25', '26'])).
% 1.61/1.79  thf('28', plain,
% 1.61/1.79      (![X0 : $i]:
% 1.61/1.79         ((k1_xboole_0) = (k3_xboole_0 @ sk_B_1 @ (k3_xboole_0 @ sk_A @ X0)))),
% 1.61/1.79      inference('demod', [status(thm)], ['22', '27'])).
% 1.61/1.79  thf('29', plain,
% 1.61/1.79      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.61/1.79      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.61/1.79  thf('30', plain,
% 1.61/1.79      (![X4 : $i, X5 : $i]:
% 1.61/1.79         ((r1_xboole_0 @ X4 @ X5)
% 1.61/1.79          | (r2_hidden @ (sk_C @ X5 @ X4) @ (k3_xboole_0 @ X4 @ X5)))),
% 1.61/1.79      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.61/1.79  thf('31', plain,
% 1.61/1.79      (![X15 : $i, X16 : $i]:
% 1.61/1.79         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 1.61/1.79           = (k3_xboole_0 @ X15 @ X16))),
% 1.61/1.79      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.61/1.79  thf(t49_xboole_1, axiom,
% 1.61/1.79    (![A:$i,B:$i,C:$i]:
% 1.61/1.79     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 1.61/1.79       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 1.61/1.79  thf('32', plain,
% 1.61/1.79      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.61/1.79         ((k3_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X19))
% 1.61/1.79           = (k4_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ X19))),
% 1.61/1.79      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.61/1.79  thf('33', plain,
% 1.61/1.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.61/1.79         ((k3_xboole_0 @ X2 @ 
% 1.61/1.79           (k4_xboole_0 @ X1 @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)))
% 1.61/1.79           = (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 1.61/1.79      inference('sup+', [status(thm)], ['31', '32'])).
% 1.61/1.79  thf('34', plain,
% 1.61/1.79      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.61/1.79         ((k3_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X19))
% 1.61/1.79           = (k4_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ X19))),
% 1.61/1.79      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.61/1.79  thf('35', plain,
% 1.61/1.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.61/1.79         ((k3_xboole_0 @ X2 @ 
% 1.61/1.79           (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))
% 1.61/1.79           = (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 1.61/1.79      inference('demod', [status(thm)], ['33', '34'])).
% 1.61/1.79  thf(t50_xboole_1, axiom,
% 1.61/1.79    (![A:$i,B:$i,C:$i]:
% 1.61/1.79     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 1.61/1.79       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 1.61/1.79  thf('36', plain,
% 1.61/1.79      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.61/1.79         ((k3_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X22))
% 1.61/1.79           = (k4_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ 
% 1.61/1.79              (k3_xboole_0 @ X20 @ X22)))),
% 1.61/1.79      inference('cnf', [status(esa)], [t50_xboole_1])).
% 1.61/1.79  thf('37', plain,
% 1.61/1.79      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.61/1.79         ((k3_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X19))
% 1.61/1.79           = (k4_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ X19))),
% 1.61/1.79      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.61/1.79  thf('38', plain,
% 1.61/1.79      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.61/1.79         ((k3_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X22))
% 1.61/1.79           = (k3_xboole_0 @ X20 @ 
% 1.61/1.79              (k4_xboole_0 @ X21 @ (k3_xboole_0 @ X20 @ X22))))),
% 1.61/1.79      inference('demod', [status(thm)], ['36', '37'])).
% 1.61/1.79  thf('39', plain,
% 1.61/1.79      (![X15 : $i, X16 : $i]:
% 1.61/1.79         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 1.61/1.79           = (k3_xboole_0 @ X15 @ X16))),
% 1.61/1.79      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.61/1.79  thf('40', plain,
% 1.61/1.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.61/1.79         ((k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.61/1.79           = (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 1.61/1.79      inference('demod', [status(thm)], ['35', '38', '39'])).
% 1.61/1.79  thf('41', plain,
% 1.61/1.79      (![X4 : $i, X6 : $i, X7 : $i]:
% 1.61/1.79         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 1.61/1.79          | ~ (r1_xboole_0 @ X4 @ X7))),
% 1.61/1.79      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.61/1.79  thf('42', plain,
% 1.61/1.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.61/1.79         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 1.61/1.79          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 1.61/1.79      inference('sup-', [status(thm)], ['40', '41'])).
% 1.61/1.79  thf('43', plain,
% 1.61/1.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.61/1.79         ((r1_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.61/1.79          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 1.61/1.79      inference('sup-', [status(thm)], ['30', '42'])).
% 1.61/1.79  thf('44', plain,
% 1.61/1.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.61/1.79         (~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.61/1.79          | (r1_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 1.61/1.79      inference('sup-', [status(thm)], ['29', '43'])).
% 1.61/1.79  thf('45', plain,
% 1.61/1.79      (![X0 : $i, X1 : $i]:
% 1.61/1.79         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 1.61/1.79          | (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ X1) @ 
% 1.61/1.79             (k3_xboole_0 @ sk_B_1 @ X0)))),
% 1.61/1.79      inference('sup-', [status(thm)], ['28', '44'])).
% 1.61/1.79  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 1.61/1.79  thf('46', plain, (![X26 : $i]: (r1_xboole_0 @ X26 @ k1_xboole_0)),
% 1.61/1.79      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.61/1.79  thf(symmetry_r1_xboole_0, axiom,
% 1.61/1.79    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.61/1.79  thf('47', plain,
% 1.61/1.79      (![X2 : $i, X3 : $i]:
% 1.61/1.79         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 1.61/1.79      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.61/1.79  thf('48', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.61/1.79      inference('sup-', [status(thm)], ['46', '47'])).
% 1.61/1.79  thf('49', plain,
% 1.61/1.79      (![X0 : $i, X1 : $i]:
% 1.61/1.79         (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ X1) @ (k3_xboole_0 @ sk_B_1 @ X0))),
% 1.61/1.79      inference('demod', [status(thm)], ['45', '48'])).
% 1.61/1.79  thf('50', plain, ($false), inference('demod', [status(thm)], ['3', '49'])).
% 1.61/1.79  
% 1.61/1.79  % SZS output end Refutation
% 1.61/1.79  
% 1.61/1.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
