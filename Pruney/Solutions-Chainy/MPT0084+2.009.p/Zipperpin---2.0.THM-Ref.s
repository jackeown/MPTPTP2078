%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7TmxK72Wtq

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:20 EST 2020

% Result     : Theorem 0.98s
% Output     : Refutation 0.98s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 120 expanded)
%              Number of leaves         :   20 (  45 expanded)
%              Depth                    :   19
%              Number of atoms          :  507 ( 848 expanded)
%              Number of equality atoms :   24 (  37 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t77_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ( r1_tarski @ A @ C )
          & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ),
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
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('12',plain,(
    r1_tarski @ k1_xboole_0 @ sk_A ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('13',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X19 @ X20 )
      | ( r1_xboole_0 @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('16',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('24',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    r1_tarski @ k1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X19 @ X20 )
      | ( r1_xboole_0 @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['21','28'])).

thf('30',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('31',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X19 @ X20 )
      | ( r1_xboole_0 @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t75_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) )).

thf('35',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_xboole_0 @ X21 @ X22 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t75_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('40',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('41',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('44',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('45',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('46',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    r1_tarski @ sk_A @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t27_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D ) )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ ( k3_xboole_0 @ B @ D ) ) ) )).

thf('49',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ ( k3_xboole_0 @ X11 @ X13 ) @ ( k3_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t27_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X3 ) @ ( k3_xboole_0 @ X0 @ X2 ) )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['46','51'])).

thf('53',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X19 @ X20 )
      | ( r1_xboole_0 @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_A ) @ X1 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_C_1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['8','54'])).

thf('56',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_xboole_0 @ X21 @ X22 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t75_xboole_1])).

thf('57',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('59',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['0','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7TmxK72Wtq
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:24:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.98/1.17  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.98/1.17  % Solved by: fo/fo7.sh
% 0.98/1.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.98/1.17  % done 921 iterations in 0.694s
% 0.98/1.17  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.98/1.17  % SZS output start Refutation
% 0.98/1.17  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.98/1.17  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.98/1.17  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.98/1.17  thf(sk_A_type, type, sk_A: $i).
% 0.98/1.17  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.98/1.17  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.98/1.17  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.98/1.17  thf(sk_B_type, type, sk_B: $i).
% 0.98/1.17  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.98/1.17  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.98/1.17  thf(t77_xboole_1, conjecture,
% 0.98/1.17    (![A:$i,B:$i,C:$i]:
% 0.98/1.17     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.98/1.17          ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 0.98/1.17  thf(zf_stmt_0, negated_conjecture,
% 0.98/1.17    (~( ![A:$i,B:$i,C:$i]:
% 0.98/1.17        ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.98/1.17             ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )),
% 0.98/1.17    inference('cnf.neg', [status(esa)], [t77_xboole_1])).
% 0.98/1.17  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf('1', plain, ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1))),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf(d7_xboole_0, axiom,
% 0.98/1.17    (![A:$i,B:$i]:
% 0.98/1.17     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.98/1.17       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.98/1.17  thf('2', plain,
% 0.98/1.17      (![X2 : $i, X3 : $i]:
% 0.98/1.17         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.98/1.17      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.98/1.17  thf('3', plain,
% 0.98/1.17      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1)) = (k1_xboole_0))),
% 0.98/1.17      inference('sup-', [status(thm)], ['1', '2'])).
% 0.98/1.17  thf(commutativity_k3_xboole_0, axiom,
% 0.98/1.17    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.98/1.17  thf('4', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.98/1.17      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.98/1.17  thf('5', plain,
% 0.98/1.17      (![X2 : $i, X4 : $i]:
% 0.98/1.17         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.98/1.17      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.98/1.17  thf('6', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]:
% 0.98/1.17         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 0.98/1.17      inference('sup-', [status(thm)], ['4', '5'])).
% 0.98/1.17  thf('7', plain,
% 0.98/1.17      ((((k1_xboole_0) != (k1_xboole_0))
% 0.98/1.17        | (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C_1) @ sk_A))),
% 0.98/1.17      inference('sup-', [status(thm)], ['3', '6'])).
% 0.98/1.17  thf('8', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C_1) @ sk_A)),
% 0.98/1.17      inference('simplify', [status(thm)], ['7'])).
% 0.98/1.17  thf('9', plain, ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1))),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf('10', plain,
% 0.98/1.17      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1)) = (k1_xboole_0))),
% 0.98/1.17      inference('sup-', [status(thm)], ['1', '2'])).
% 0.98/1.17  thf(t17_xboole_1, axiom,
% 0.98/1.17    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.98/1.17  thf('11', plain,
% 0.98/1.17      (![X9 : $i, X10 : $i]: (r1_tarski @ (k3_xboole_0 @ X9 @ X10) @ X9)),
% 0.98/1.17      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.98/1.17  thf('12', plain, ((r1_tarski @ k1_xboole_0 @ sk_A)),
% 0.98/1.17      inference('sup+', [status(thm)], ['10', '11'])).
% 0.98/1.17  thf(t63_xboole_1, axiom,
% 0.98/1.17    (![A:$i,B:$i,C:$i]:
% 0.98/1.17     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.98/1.17       ( r1_xboole_0 @ A @ C ) ))).
% 0.98/1.17  thf('13', plain,
% 0.98/1.17      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.98/1.17         (~ (r1_tarski @ X18 @ X19)
% 0.98/1.17          | ~ (r1_xboole_0 @ X19 @ X20)
% 0.98/1.17          | (r1_xboole_0 @ X18 @ X20))),
% 0.98/1.17      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.98/1.17  thf('14', plain,
% 0.98/1.17      (![X0 : $i]:
% 0.98/1.17         ((r1_xboole_0 @ k1_xboole_0 @ X0) | ~ (r1_xboole_0 @ sk_A @ X0))),
% 0.98/1.17      inference('sup-', [status(thm)], ['12', '13'])).
% 0.98/1.17  thf('15', plain,
% 0.98/1.17      ((r1_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C_1))),
% 0.98/1.17      inference('sup-', [status(thm)], ['9', '14'])).
% 0.98/1.17  thf(t4_xboole_0, axiom,
% 0.98/1.17    (![A:$i,B:$i]:
% 0.98/1.17     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.98/1.17            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.98/1.17       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.98/1.17            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.98/1.17  thf('16', plain,
% 0.98/1.17      (![X5 : $i, X6 : $i]:
% 0.98/1.17         ((r1_xboole_0 @ X5 @ X6)
% 0.98/1.17          | (r2_hidden @ (sk_C @ X6 @ X5) @ (k3_xboole_0 @ X5 @ X6)))),
% 0.98/1.17      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.98/1.17  thf('17', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.98/1.17      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.98/1.17  thf('18', plain,
% 0.98/1.17      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.98/1.17         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.98/1.17          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.98/1.17      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.98/1.17  thf('19', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.98/1.17         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.98/1.17          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.98/1.17      inference('sup-', [status(thm)], ['17', '18'])).
% 0.98/1.17  thf('20', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]:
% 0.98/1.17         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.98/1.17      inference('sup-', [status(thm)], ['16', '19'])).
% 0.98/1.17  thf('21', plain,
% 0.98/1.17      ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C_1) @ k1_xboole_0)),
% 0.98/1.17      inference('sup-', [status(thm)], ['15', '20'])).
% 0.98/1.17  thf('22', plain,
% 0.98/1.17      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1)) = (k1_xboole_0))),
% 0.98/1.17      inference('sup-', [status(thm)], ['1', '2'])).
% 0.98/1.17  thf('23', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.98/1.17      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.98/1.17  thf('24', plain,
% 0.98/1.17      (![X9 : $i, X10 : $i]: (r1_tarski @ (k3_xboole_0 @ X9 @ X10) @ X9)),
% 0.98/1.17      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.98/1.17  thf('25', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.98/1.17      inference('sup+', [status(thm)], ['23', '24'])).
% 0.98/1.17  thf('26', plain, ((r1_tarski @ k1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C_1))),
% 0.98/1.17      inference('sup+', [status(thm)], ['22', '25'])).
% 0.98/1.17  thf('27', plain,
% 0.98/1.17      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.98/1.17         (~ (r1_tarski @ X18 @ X19)
% 0.98/1.17          | ~ (r1_xboole_0 @ X19 @ X20)
% 0.98/1.17          | (r1_xboole_0 @ X18 @ X20))),
% 0.98/1.17      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.98/1.17  thf('28', plain,
% 0.98/1.17      (![X0 : $i]:
% 0.98/1.17         ((r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.98/1.17          | ~ (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C_1) @ X0))),
% 0.98/1.17      inference('sup-', [status(thm)], ['26', '27'])).
% 0.98/1.17  thf('29', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.98/1.17      inference('sup-', [status(thm)], ['21', '28'])).
% 0.98/1.17  thf('30', plain,
% 0.98/1.17      (![X9 : $i, X10 : $i]: (r1_tarski @ (k3_xboole_0 @ X9 @ X10) @ X9)),
% 0.98/1.17      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.98/1.17  thf('31', plain,
% 0.98/1.17      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.98/1.17         (~ (r1_tarski @ X18 @ X19)
% 0.98/1.17          | ~ (r1_xboole_0 @ X19 @ X20)
% 0.98/1.17          | (r1_xboole_0 @ X18 @ X20))),
% 0.98/1.17      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.98/1.17  thf('32', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.98/1.17         ((r1_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2)
% 0.98/1.17          | ~ (r1_xboole_0 @ X0 @ X2))),
% 0.98/1.17      inference('sup-', [status(thm)], ['30', '31'])).
% 0.98/1.17  thf('33', plain,
% 0.98/1.17      (![X0 : $i]:
% 0.98/1.17         (r1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0)),
% 0.98/1.17      inference('sup-', [status(thm)], ['29', '32'])).
% 0.98/1.17  thf('34', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.98/1.17      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.98/1.17  thf(t75_xboole_1, axiom,
% 0.98/1.17    (![A:$i,B:$i]:
% 0.98/1.17     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.98/1.17          ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) ))).
% 0.98/1.17  thf('35', plain,
% 0.98/1.17      (![X21 : $i, X22 : $i]:
% 0.98/1.17         ((r1_xboole_0 @ X21 @ X22)
% 0.98/1.17          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ X22))),
% 0.98/1.17      inference('cnf', [status(esa)], [t75_xboole_1])).
% 0.98/1.17  thf('36', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]:
% 0.98/1.17         (~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 0.98/1.17          | (r1_xboole_0 @ X0 @ X1))),
% 0.98/1.17      inference('sup-', [status(thm)], ['34', '35'])).
% 0.98/1.17  thf('37', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.98/1.17      inference('sup-', [status(thm)], ['33', '36'])).
% 0.98/1.17  thf('38', plain,
% 0.98/1.17      (![X2 : $i, X3 : $i]:
% 0.98/1.17         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.98/1.17      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.98/1.17  thf('39', plain,
% 0.98/1.17      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.98/1.17      inference('sup-', [status(thm)], ['37', '38'])).
% 0.98/1.17  thf(t48_xboole_1, axiom,
% 0.98/1.17    (![A:$i,B:$i]:
% 0.98/1.17     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.98/1.17  thf('40', plain,
% 0.98/1.17      (![X16 : $i, X17 : $i]:
% 0.98/1.17         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.98/1.17           = (k3_xboole_0 @ X16 @ X17))),
% 0.98/1.17      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.98/1.17  thf('41', plain,
% 0.98/1.17      (![X16 : $i, X17 : $i]:
% 0.98/1.17         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.98/1.17           = (k3_xboole_0 @ X16 @ X17))),
% 0.98/1.17      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.98/1.17  thf('42', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]:
% 0.98/1.17         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.98/1.17           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.98/1.17      inference('sup+', [status(thm)], ['40', '41'])).
% 0.98/1.17  thf('43', plain,
% 0.98/1.17      (![X0 : $i]:
% 0.98/1.17         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.98/1.17           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.98/1.17      inference('sup+', [status(thm)], ['39', '42'])).
% 0.98/1.17  thf(t3_boole, axiom,
% 0.98/1.17    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.98/1.17  thf('44', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.98/1.17      inference('cnf', [status(esa)], [t3_boole])).
% 0.98/1.17  thf('45', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.98/1.17      inference('cnf', [status(esa)], [t3_boole])).
% 0.98/1.17  thf('46', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.98/1.17      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.98/1.17  thf('47', plain, ((r1_tarski @ sk_A @ sk_C_1)),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf('48', plain,
% 0.98/1.17      (![X9 : $i, X10 : $i]: (r1_tarski @ (k3_xboole_0 @ X9 @ X10) @ X9)),
% 0.98/1.17      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.98/1.17  thf(t27_xboole_1, axiom,
% 0.98/1.17    (![A:$i,B:$i,C:$i,D:$i]:
% 0.98/1.17     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.98/1.17       ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ ( k3_xboole_0 @ B @ D ) ) ))).
% 0.98/1.17  thf('49', plain,
% 0.98/1.17      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.98/1.17         (~ (r1_tarski @ X11 @ X12)
% 0.98/1.17          | ~ (r1_tarski @ X13 @ X14)
% 0.98/1.17          | (r1_tarski @ (k3_xboole_0 @ X11 @ X13) @ (k3_xboole_0 @ X12 @ X14)))),
% 0.98/1.17      inference('cnf', [status(esa)], [t27_xboole_1])).
% 0.98/1.17  thf('50', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.98/1.17         ((r1_tarski @ (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X3) @ 
% 0.98/1.17           (k3_xboole_0 @ X0 @ X2))
% 0.98/1.17          | ~ (r1_tarski @ X3 @ X2))),
% 0.98/1.17      inference('sup-', [status(thm)], ['48', '49'])).
% 0.98/1.17  thf('51', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]:
% 0.98/1.17         (r1_tarski @ (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ sk_A) @ 
% 0.98/1.17          (k3_xboole_0 @ X0 @ sk_C_1))),
% 0.98/1.17      inference('sup-', [status(thm)], ['47', '50'])).
% 0.98/1.17  thf('52', plain,
% 0.98/1.17      (![X0 : $i]:
% 0.98/1.17         (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ (k3_xboole_0 @ X0 @ sk_C_1))),
% 0.98/1.17      inference('sup+', [status(thm)], ['46', '51'])).
% 0.98/1.17  thf('53', plain,
% 0.98/1.17      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.98/1.17         (~ (r1_tarski @ X18 @ X19)
% 0.98/1.17          | ~ (r1_xboole_0 @ X19 @ X20)
% 0.98/1.17          | (r1_xboole_0 @ X18 @ X20))),
% 0.98/1.17      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.98/1.17  thf('54', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]:
% 0.98/1.17         ((r1_xboole_0 @ (k3_xboole_0 @ X0 @ sk_A) @ X1)
% 0.98/1.17          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X0 @ sk_C_1) @ X1))),
% 0.98/1.17      inference('sup-', [status(thm)], ['52', '53'])).
% 0.98/1.17  thf('55', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_A)),
% 0.98/1.17      inference('sup-', [status(thm)], ['8', '54'])).
% 0.98/1.17  thf('56', plain,
% 0.98/1.17      (![X21 : $i, X22 : $i]:
% 0.98/1.17         ((r1_xboole_0 @ X21 @ X22)
% 0.98/1.17          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ X22))),
% 0.98/1.17      inference('cnf', [status(esa)], [t75_xboole_1])).
% 0.98/1.17  thf('57', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 0.98/1.17      inference('sup-', [status(thm)], ['55', '56'])).
% 0.98/1.17  thf('58', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i]:
% 0.98/1.17         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.98/1.17      inference('sup-', [status(thm)], ['16', '19'])).
% 0.98/1.17  thf('59', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.98/1.17      inference('sup-', [status(thm)], ['57', '58'])).
% 0.98/1.17  thf('60', plain, ($false), inference('demod', [status(thm)], ['0', '59'])).
% 0.98/1.17  
% 0.98/1.17  % SZS output end Refutation
% 0.98/1.17  
% 0.98/1.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
