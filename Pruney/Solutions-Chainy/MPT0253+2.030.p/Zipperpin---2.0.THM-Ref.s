%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ygRzWmHNxl

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:34 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 141 expanded)
%              Number of leaves         :   27 (  55 expanded)
%              Depth                    :   19
%              Number of atoms          :  544 ( 957 expanded)
%              Number of equality atoms :   58 ( 107 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t48_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ C @ B ) )
     => ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ C @ B ) )
       => ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t48_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X52: $i,X54: $i,X55: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X52 @ X54 ) @ X55 )
      | ~ ( r2_hidden @ X54 @ X55 )
      | ~ ( r2_hidden @ X52 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_C_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_C_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('6',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_1 ) @ sk_B_1 )
    = ( k2_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('8',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k2_tarski @ sk_A @ sk_C_1 ) )
    = ( k2_tarski @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('10',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k2_tarski @ sk_A @ sk_C_1 ) )
    = ( k5_xboole_0 @ sk_B_1 @ ( k2_tarski @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('12',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('17',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('20',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('23',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('26',plain,(
    ! [X17: $i] :
      ( r1_xboole_0 @ X17 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('36',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','39'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('41',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','44'])).

thf('46',plain,
    ( sk_B_1
    = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ sk_B_1 @ ( k2_tarski @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['10','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('48',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('49',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('50',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['46','53'])).

thf('55',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_1 ) @ sk_B_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['54','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ygRzWmHNxl
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:22:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.40/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.59  % Solved by: fo/fo7.sh
% 0.40/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.59  % done 282 iterations in 0.119s
% 0.40/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.59  % SZS output start Refutation
% 0.40/0.59  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.40/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.59  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.40/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.40/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.40/0.59  thf(sk_B_type, type, sk_B: $i > $i).
% 0.40/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.40/0.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.40/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.59  thf(t48_zfmisc_1, conjecture,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.40/0.59       ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( B ) ) ))).
% 0.40/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.59    (~( ![A:$i,B:$i,C:$i]:
% 0.40/0.59        ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.40/0.59          ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( B ) ) ) )),
% 0.40/0.59    inference('cnf.neg', [status(esa)], [t48_zfmisc_1])).
% 0.40/0.59  thf('0', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('1', plain, ((r2_hidden @ sk_C_1 @ sk_B_1)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(t38_zfmisc_1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.40/0.59       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.40/0.59  thf('2', plain,
% 0.40/0.59      (![X52 : $i, X54 : $i, X55 : $i]:
% 0.40/0.59         ((r1_tarski @ (k2_tarski @ X52 @ X54) @ X55)
% 0.40/0.59          | ~ (r2_hidden @ X54 @ X55)
% 0.40/0.59          | ~ (r2_hidden @ X52 @ X55))),
% 0.40/0.59      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.40/0.59  thf('3', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (r2_hidden @ X0 @ sk_B_1)
% 0.40/0.59          | (r1_tarski @ (k2_tarski @ X0 @ sk_C_1) @ sk_B_1))),
% 0.40/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.59  thf('4', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_C_1) @ sk_B_1)),
% 0.40/0.59      inference('sup-', [status(thm)], ['0', '3'])).
% 0.40/0.59  thf(t28_xboole_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.40/0.59  thf('5', plain,
% 0.40/0.59      (![X12 : $i, X13 : $i]:
% 0.40/0.59         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.40/0.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.40/0.59  thf('6', plain,
% 0.40/0.59      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_C_1) @ sk_B_1)
% 0.40/0.59         = (k2_tarski @ sk_A @ sk_C_1))),
% 0.40/0.59      inference('sup-', [status(thm)], ['4', '5'])).
% 0.40/0.59  thf(commutativity_k3_xboole_0, axiom,
% 0.40/0.59    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.40/0.59  thf('7', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.40/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.40/0.59  thf('8', plain,
% 0.40/0.59      (((k3_xboole_0 @ sk_B_1 @ (k2_tarski @ sk_A @ sk_C_1))
% 0.40/0.59         = (k2_tarski @ sk_A @ sk_C_1))),
% 0.40/0.59      inference('demod', [status(thm)], ['6', '7'])).
% 0.40/0.59  thf(t100_xboole_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.40/0.59  thf('9', plain,
% 0.40/0.59      (![X10 : $i, X11 : $i]:
% 0.40/0.59         ((k4_xboole_0 @ X10 @ X11)
% 0.40/0.59           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.40/0.59  thf('10', plain,
% 0.40/0.59      (((k4_xboole_0 @ sk_B_1 @ (k2_tarski @ sk_A @ sk_C_1))
% 0.40/0.59         = (k5_xboole_0 @ sk_B_1 @ (k2_tarski @ sk_A @ sk_C_1)))),
% 0.40/0.59      inference('sup+', [status(thm)], ['8', '9'])).
% 0.40/0.59  thf(commutativity_k5_xboole_0, axiom,
% 0.40/0.59    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.40/0.59  thf('11', plain,
% 0.40/0.59      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.40/0.59      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.40/0.59  thf(idempotence_k3_xboole_0, axiom,
% 0.40/0.59    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.40/0.59  thf('12', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 0.40/0.59      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.40/0.59  thf('13', plain,
% 0.40/0.59      (![X10 : $i, X11 : $i]:
% 0.40/0.59         ((k4_xboole_0 @ X10 @ X11)
% 0.40/0.59           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.40/0.59  thf('14', plain,
% 0.40/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['12', '13'])).
% 0.40/0.59  thf('15', plain,
% 0.40/0.59      (![X10 : $i, X11 : $i]:
% 0.40/0.59         ((k4_xboole_0 @ X10 @ X11)
% 0.40/0.59           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.40/0.59  thf('16', plain,
% 0.40/0.59      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.40/0.59      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.40/0.59  thf(t5_boole, axiom,
% 0.40/0.59    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.40/0.59  thf('17', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.40/0.59      inference('cnf', [status(esa)], [t5_boole])).
% 0.40/0.59  thf('18', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['16', '17'])).
% 0.40/0.59  thf('19', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['15', '18'])).
% 0.40/0.59  thf(t7_xboole_0, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.40/0.59          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.40/0.59  thf('20', plain,
% 0.40/0.59      (![X9 : $i]: (((X9) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X9) @ X9))),
% 0.40/0.59      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.40/0.59  thf('21', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['15', '18'])).
% 0.40/0.59  thf('22', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.40/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.40/0.59  thf(t4_xboole_0, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.40/0.59            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.40/0.59       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.40/0.59            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.40/0.59  thf('23', plain,
% 0.40/0.59      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.40/0.59         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.40/0.59          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.40/0.59      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.40/0.59  thf('24', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.40/0.59          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.40/0.59      inference('sup-', [status(thm)], ['22', '23'])).
% 0.40/0.59  thf('25', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))
% 0.40/0.59          | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['21', '24'])).
% 0.40/0.59  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.40/0.59  thf('26', plain, (![X17 : $i]: (r1_xboole_0 @ X17 @ k1_xboole_0)),
% 0.40/0.59      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.40/0.59  thf('27', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         ~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.40/0.59      inference('demod', [status(thm)], ['25', '26'])).
% 0.40/0.59  thf('28', plain,
% 0.40/0.59      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['20', '27'])).
% 0.40/0.59  thf('29', plain,
% 0.40/0.59      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.40/0.59      inference('demod', [status(thm)], ['19', '28'])).
% 0.40/0.59  thf('30', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.40/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.40/0.59  thf('31', plain,
% 0.40/0.59      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['29', '30'])).
% 0.40/0.59  thf('32', plain,
% 0.40/0.59      (![X10 : $i, X11 : $i]:
% 0.40/0.59         ((k4_xboole_0 @ X10 @ X11)
% 0.40/0.59           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.40/0.59  thf('33', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['31', '32'])).
% 0.40/0.59  thf('34', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.40/0.59      inference('cnf', [status(esa)], [t5_boole])).
% 0.40/0.59  thf('35', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['33', '34'])).
% 0.40/0.59  thf(t48_xboole_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.40/0.59  thf('36', plain,
% 0.40/0.59      (![X14 : $i, X15 : $i]:
% 0.40/0.59         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.40/0.59           = (k3_xboole_0 @ X14 @ X15))),
% 0.40/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.40/0.59  thf('37', plain,
% 0.40/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['35', '36'])).
% 0.40/0.59  thf('38', plain,
% 0.40/0.59      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['29', '30'])).
% 0.40/0.59  thf('39', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.40/0.59      inference('demod', [status(thm)], ['37', '38'])).
% 0.40/0.59  thf('40', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.40/0.59      inference('demod', [status(thm)], ['14', '39'])).
% 0.40/0.59  thf(t91_xboole_1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.40/0.59       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.40/0.59  thf('41', plain,
% 0.40/0.59      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.40/0.59         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 0.40/0.59           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.40/0.59  thf('42', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.40/0.59           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.40/0.59      inference('sup+', [status(thm)], ['40', '41'])).
% 0.40/0.59  thf('43', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['16', '17'])).
% 0.40/0.59  thf('44', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.40/0.59      inference('demod', [status(thm)], ['42', '43'])).
% 0.40/0.59  thf('45', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.40/0.59      inference('sup+', [status(thm)], ['11', '44'])).
% 0.40/0.59  thf('46', plain,
% 0.40/0.59      (((sk_B_1)
% 0.40/0.59         = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_C_1) @ 
% 0.40/0.59            (k4_xboole_0 @ sk_B_1 @ (k2_tarski @ sk_A @ sk_C_1))))),
% 0.40/0.59      inference('sup+', [status(thm)], ['10', '45'])).
% 0.40/0.59  thf('47', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.40/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.40/0.59  thf(t94_xboole_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( k2_xboole_0 @ A @ B ) =
% 0.40/0.59       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.40/0.59  thf('48', plain,
% 0.40/0.59      (![X21 : $i, X22 : $i]:
% 0.40/0.59         ((k2_xboole_0 @ X21 @ X22)
% 0.40/0.59           = (k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ 
% 0.40/0.59              (k3_xboole_0 @ X21 @ X22)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.40/0.59  thf('49', plain,
% 0.40/0.59      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.40/0.59         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 0.40/0.59           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.40/0.59  thf('50', plain,
% 0.40/0.59      (![X21 : $i, X22 : $i]:
% 0.40/0.59         ((k2_xboole_0 @ X21 @ X22)
% 0.40/0.59           = (k5_xboole_0 @ X21 @ 
% 0.40/0.59              (k5_xboole_0 @ X22 @ (k3_xboole_0 @ X21 @ X22))))),
% 0.40/0.59      inference('demod', [status(thm)], ['48', '49'])).
% 0.40/0.59  thf('51', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         ((k2_xboole_0 @ X0 @ X1)
% 0.40/0.59           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.40/0.59      inference('sup+', [status(thm)], ['47', '50'])).
% 0.40/0.59  thf('52', plain,
% 0.40/0.59      (![X10 : $i, X11 : $i]:
% 0.40/0.59         ((k4_xboole_0 @ X10 @ X11)
% 0.40/0.59           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.40/0.59  thf('53', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         ((k2_xboole_0 @ X0 @ X1)
% 0.40/0.59           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.40/0.59      inference('demod', [status(thm)], ['51', '52'])).
% 0.40/0.59  thf('54', plain,
% 0.40/0.59      (((sk_B_1) = (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_C_1) @ sk_B_1))),
% 0.40/0.59      inference('demod', [status(thm)], ['46', '53'])).
% 0.40/0.59  thf('55', plain,
% 0.40/0.59      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_C_1) @ sk_B_1) != (sk_B_1))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('56', plain, ($false),
% 0.40/0.59      inference('simplify_reflect-', [status(thm)], ['54', '55'])).
% 0.40/0.59  
% 0.40/0.59  % SZS output end Refutation
% 0.40/0.59  
% 0.40/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
