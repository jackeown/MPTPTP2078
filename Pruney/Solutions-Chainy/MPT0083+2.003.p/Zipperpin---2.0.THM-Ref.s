%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iIwovxACbN

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:15 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 167 expanded)
%              Number of leaves         :   21 (  62 expanded)
%              Depth                    :   14
%              Number of atoms          :  502 (1349 expanded)
%              Number of equality atoms :   35 (  85 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ ( k3_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('6',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('7',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X13: $i] :
      ( ( k3_xboole_0 @ X13 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('13',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ ( k3_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('14',plain,(
    ! [X23: $i,X24: $i,X26: $i] :
      ( ( r1_xboole_0 @ X23 @ X26 )
      | ~ ( r1_xboole_0 @ X23 @ ( k2_xboole_0 @ X24 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ X3 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_xboole_0 @ X3 @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ k1_xboole_0 )
      | ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('17',plain,(
    ! [X22: $i] :
      ( r1_xboole_0 @ X22 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('19',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X7 ) @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('20',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('21',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ X7 @ X10 ) )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['18','27'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('29',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ X3 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_xboole_0 @ X3 @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['7','32'])).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
      = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('39',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('41',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('48',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['39','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['0','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iIwovxACbN
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:02:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.90/1.06  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.90/1.06  % Solved by: fo/fo7.sh
% 0.90/1.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.06  % done 2102 iterations in 0.614s
% 0.90/1.06  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.90/1.06  % SZS output start Refutation
% 0.90/1.06  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.90/1.06  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.90/1.06  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.90/1.06  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.06  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.90/1.06  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.90/1.06  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.90/1.06  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.90/1.06  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.90/1.06  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.06  thf(t76_xboole_1, conjecture,
% 0.90/1.06    (![A:$i,B:$i,C:$i]:
% 0.90/1.06     ( ( r1_xboole_0 @ A @ B ) =>
% 0.90/1.06       ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ))).
% 0.90/1.06  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.06    (~( ![A:$i,B:$i,C:$i]:
% 0.90/1.06        ( ( r1_xboole_0 @ A @ B ) =>
% 0.90/1.06          ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ) )),
% 0.90/1.06    inference('cnf.neg', [status(esa)], [t76_xboole_1])).
% 0.90/1.06  thf('0', plain,
% 0.90/1.06      (~ (r1_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ 
% 0.90/1.06          (k3_xboole_0 @ sk_C_1 @ sk_B))),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('1', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf(d7_xboole_0, axiom,
% 0.90/1.06    (![A:$i,B:$i]:
% 0.90/1.06     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.90/1.06       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.90/1.06  thf('2', plain,
% 0.90/1.06      (![X2 : $i, X3 : $i]:
% 0.90/1.06         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.90/1.06      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.90/1.06  thf('3', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.90/1.06      inference('sup-', [status(thm)], ['1', '2'])).
% 0.90/1.06  thf(t47_xboole_1, axiom,
% 0.90/1.06    (![A:$i,B:$i]:
% 0.90/1.06     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.90/1.06  thf('4', plain,
% 0.90/1.06      (![X15 : $i, X16 : $i]:
% 0.90/1.06         ((k4_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16))
% 0.90/1.06           = (k4_xboole_0 @ X15 @ X16))),
% 0.90/1.06      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.90/1.06  thf('5', plain,
% 0.90/1.06      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.90/1.06      inference('sup+', [status(thm)], ['3', '4'])).
% 0.90/1.06  thf(t3_boole, axiom,
% 0.90/1.06    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.90/1.06  thf('6', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.90/1.06      inference('cnf', [status(esa)], [t3_boole])).
% 0.90/1.06  thf('7', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.90/1.06      inference('demod', [status(thm)], ['5', '6'])).
% 0.90/1.06  thf('8', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.90/1.06      inference('cnf', [status(esa)], [t3_boole])).
% 0.90/1.06  thf(t48_xboole_1, axiom,
% 0.90/1.06    (![A:$i,B:$i]:
% 0.90/1.06     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.90/1.06  thf('9', plain,
% 0.90/1.06      (![X17 : $i, X18 : $i]:
% 0.90/1.06         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.90/1.06           = (k3_xboole_0 @ X17 @ X18))),
% 0.90/1.06      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.90/1.06  thf('10', plain,
% 0.90/1.06      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.90/1.06      inference('sup+', [status(thm)], ['8', '9'])).
% 0.90/1.06  thf(t2_boole, axiom,
% 0.90/1.06    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.90/1.06  thf('11', plain,
% 0.90/1.06      (![X13 : $i]: ((k3_xboole_0 @ X13 @ k1_xboole_0) = (k1_xboole_0))),
% 0.90/1.06      inference('cnf', [status(esa)], [t2_boole])).
% 0.90/1.06  thf('12', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.90/1.06      inference('demod', [status(thm)], ['10', '11'])).
% 0.90/1.06  thf(t52_xboole_1, axiom,
% 0.90/1.06    (![A:$i,B:$i,C:$i]:
% 0.90/1.06     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.90/1.06       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.90/1.06  thf('13', plain,
% 0.90/1.06      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.90/1.06         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 0.90/1.06           = (k2_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ 
% 0.90/1.06              (k3_xboole_0 @ X19 @ X21)))),
% 0.90/1.06      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.90/1.06  thf(t70_xboole_1, axiom,
% 0.90/1.06    (![A:$i,B:$i,C:$i]:
% 0.90/1.06     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.90/1.06            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.90/1.06       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.90/1.06            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.90/1.06  thf('14', plain,
% 0.90/1.06      (![X23 : $i, X24 : $i, X26 : $i]:
% 0.90/1.06         ((r1_xboole_0 @ X23 @ X26)
% 0.90/1.06          | ~ (r1_xboole_0 @ X23 @ (k2_xboole_0 @ X24 @ X26)))),
% 0.90/1.06      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.90/1.06  thf('15', plain,
% 0.90/1.06      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.90/1.06         (~ (r1_xboole_0 @ X3 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 0.90/1.06          | (r1_xboole_0 @ X3 @ (k3_xboole_0 @ X2 @ X0)))),
% 0.90/1.06      inference('sup-', [status(thm)], ['13', '14'])).
% 0.90/1.06  thf('16', plain,
% 0.90/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.06         (~ (r1_xboole_0 @ X2 @ k1_xboole_0)
% 0.90/1.06          | (r1_xboole_0 @ X2 @ (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)))),
% 0.90/1.06      inference('sup-', [status(thm)], ['12', '15'])).
% 0.90/1.06  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.90/1.06  thf('17', plain, (![X22 : $i]: (r1_xboole_0 @ X22 @ k1_xboole_0)),
% 0.90/1.06      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.90/1.06  thf('18', plain,
% 0.90/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.06         (r1_xboole_0 @ X2 @ (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.90/1.06      inference('demod', [status(thm)], ['16', '17'])).
% 0.90/1.06  thf(t4_xboole_0, axiom,
% 0.90/1.06    (![A:$i,B:$i]:
% 0.90/1.06     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.90/1.06            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.90/1.06       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.90/1.06            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.90/1.06  thf('19', plain,
% 0.90/1.06      (![X7 : $i, X8 : $i]:
% 0.90/1.06         ((r1_xboole_0 @ X7 @ X8)
% 0.90/1.06          | (r2_hidden @ (sk_C @ X8 @ X7) @ (k3_xboole_0 @ X7 @ X8)))),
% 0.90/1.06      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.90/1.06  thf('20', plain,
% 0.90/1.06      (![X15 : $i, X16 : $i]:
% 0.90/1.06         ((k4_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16))
% 0.90/1.06           = (k4_xboole_0 @ X15 @ X16))),
% 0.90/1.06      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.90/1.06  thf('21', plain,
% 0.90/1.06      (![X17 : $i, X18 : $i]:
% 0.90/1.06         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.90/1.06           = (k3_xboole_0 @ X17 @ X18))),
% 0.90/1.06      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.90/1.06  thf('22', plain,
% 0.90/1.06      (![X0 : $i, X1 : $i]:
% 0.90/1.06         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.90/1.06           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.90/1.06      inference('sup+', [status(thm)], ['20', '21'])).
% 0.90/1.06  thf('23', plain,
% 0.90/1.06      (![X17 : $i, X18 : $i]:
% 0.90/1.06         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.90/1.06           = (k3_xboole_0 @ X17 @ X18))),
% 0.90/1.06      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.90/1.06  thf('24', plain,
% 0.90/1.06      (![X0 : $i, X1 : $i]:
% 0.90/1.06         ((k3_xboole_0 @ X1 @ X0)
% 0.90/1.06           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.90/1.06      inference('demod', [status(thm)], ['22', '23'])).
% 0.90/1.06  thf('25', plain,
% 0.90/1.06      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.90/1.06         (~ (r2_hidden @ X9 @ (k3_xboole_0 @ X7 @ X10))
% 0.90/1.06          | ~ (r1_xboole_0 @ X7 @ X10))),
% 0.90/1.06      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.90/1.06  thf('26', plain,
% 0.90/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.06         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.90/1.06          | ~ (r1_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.90/1.06      inference('sup-', [status(thm)], ['24', '25'])).
% 0.90/1.06  thf('27', plain,
% 0.90/1.06      (![X0 : $i, X1 : $i]:
% 0.90/1.06         ((r1_xboole_0 @ X1 @ X0)
% 0.90/1.06          | ~ (r1_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.90/1.06      inference('sup-', [status(thm)], ['19', '26'])).
% 0.90/1.06  thf('28', plain,
% 0.90/1.06      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.90/1.06      inference('sup-', [status(thm)], ['18', '27'])).
% 0.90/1.06  thf(symmetry_r1_xboole_0, axiom,
% 0.90/1.06    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.90/1.06  thf('29', plain,
% 0.90/1.06      (![X5 : $i, X6 : $i]:
% 0.90/1.06         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 0.90/1.06      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.90/1.06  thf('30', plain,
% 0.90/1.06      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.90/1.06      inference('sup-', [status(thm)], ['28', '29'])).
% 0.90/1.06  thf('31', plain,
% 0.90/1.06      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.90/1.06         (~ (r1_xboole_0 @ X3 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 0.90/1.06          | (r1_xboole_0 @ X3 @ (k3_xboole_0 @ X2 @ X0)))),
% 0.90/1.06      inference('sup-', [status(thm)], ['13', '14'])).
% 0.90/1.06  thf('32', plain,
% 0.90/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.06         (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X2 @ X0))),
% 0.90/1.06      inference('sup-', [status(thm)], ['30', '31'])).
% 0.90/1.06  thf('33', plain,
% 0.90/1.06      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k3_xboole_0 @ X0 @ sk_B))),
% 0.90/1.06      inference('sup+', [status(thm)], ['7', '32'])).
% 0.90/1.06  thf('34', plain,
% 0.90/1.06      (![X2 : $i, X3 : $i]:
% 0.90/1.06         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.90/1.06      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.90/1.06  thf('35', plain,
% 0.90/1.06      (![X0 : $i]:
% 0.90/1.06         ((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)) = (k1_xboole_0))),
% 0.90/1.06      inference('sup-', [status(thm)], ['33', '34'])).
% 0.90/1.06  thf('36', plain,
% 0.90/1.06      (![X15 : $i, X16 : $i]:
% 0.90/1.06         ((k4_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16))
% 0.90/1.06           = (k4_xboole_0 @ X15 @ X16))),
% 0.90/1.06      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.90/1.06  thf('37', plain,
% 0.90/1.06      (![X0 : $i]:
% 0.90/1.06         ((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.90/1.06           = (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)))),
% 0.90/1.06      inference('sup+', [status(thm)], ['35', '36'])).
% 0.90/1.06  thf('38', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.90/1.06      inference('cnf', [status(esa)], [t3_boole])).
% 0.90/1.06  thf('39', plain,
% 0.90/1.06      (![X0 : $i]: ((sk_A) = (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)))),
% 0.90/1.06      inference('demod', [status(thm)], ['37', '38'])).
% 0.90/1.06  thf('40', plain,
% 0.90/1.06      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.90/1.06      inference('sup-', [status(thm)], ['28', '29'])).
% 0.90/1.06  thf('41', plain,
% 0.90/1.06      (![X2 : $i, X3 : $i]:
% 0.90/1.06         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.90/1.06      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.90/1.06  thf('42', plain,
% 0.90/1.06      (![X0 : $i, X1 : $i]:
% 0.90/1.06         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.90/1.06      inference('sup-', [status(thm)], ['40', '41'])).
% 0.90/1.06  thf('43', plain,
% 0.90/1.06      (![X15 : $i, X16 : $i]:
% 0.90/1.06         ((k4_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16))
% 0.90/1.06           = (k4_xboole_0 @ X15 @ X16))),
% 0.90/1.06      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.90/1.06  thf('44', plain,
% 0.90/1.06      (![X0 : $i, X1 : $i]:
% 0.90/1.06         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.90/1.06           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.90/1.06      inference('sup+', [status(thm)], ['42', '43'])).
% 0.90/1.06  thf('45', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.90/1.06      inference('cnf', [status(esa)], [t3_boole])).
% 0.90/1.06  thf('46', plain,
% 0.90/1.06      (![X0 : $i, X1 : $i]:
% 0.90/1.06         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.90/1.06      inference('demod', [status(thm)], ['44', '45'])).
% 0.90/1.06  thf('47', plain,
% 0.90/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.06         (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X2 @ X0))),
% 0.90/1.06      inference('sup-', [status(thm)], ['30', '31'])).
% 0.90/1.06  thf('48', plain,
% 0.90/1.06      (![X5 : $i, X6 : $i]:
% 0.90/1.06         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 0.90/1.06      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.90/1.06  thf('49', plain,
% 0.90/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.06         (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X2 @ X0))),
% 0.90/1.06      inference('sup-', [status(thm)], ['47', '48'])).
% 0.90/1.06  thf('50', plain,
% 0.90/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.06         (r1_xboole_0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0)),
% 0.90/1.06      inference('sup+', [status(thm)], ['46', '49'])).
% 0.90/1.06  thf('51', plain,
% 0.90/1.06      (![X0 : $i, X1 : $i]:
% 0.90/1.06         (r1_xboole_0 @ (k3_xboole_0 @ X1 @ sk_A) @ (k3_xboole_0 @ X0 @ sk_B))),
% 0.90/1.06      inference('sup+', [status(thm)], ['39', '50'])).
% 0.90/1.06  thf('52', plain, ($false), inference('demod', [status(thm)], ['0', '51'])).
% 0.90/1.06  
% 0.90/1.06  % SZS output end Refutation
% 0.90/1.06  
% 0.90/1.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
