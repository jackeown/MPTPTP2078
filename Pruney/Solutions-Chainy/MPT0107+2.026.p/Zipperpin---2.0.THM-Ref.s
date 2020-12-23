%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7jk1weLEOg

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:13 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 319 expanded)
%              Number of leaves         :   18 ( 100 expanded)
%              Depth                    :   18
%              Number of atoms          :  581 (2558 expanded)
%              Number of equality atoms :   67 ( 239 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t100_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k4_xboole_0 @ A @ B )
        = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t100_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
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
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('10',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('11',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('17',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['17'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('19',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('20',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X12 )
      | ~ ( r2_hidden @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('28',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('30',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('36',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['28','33'])).

thf('40',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('41',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['38','39','44','45'])).

thf('47',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['28','33'])).

thf('50',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['16','48','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','58','59'])).

thf('61',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','60'])).

thf('62',plain,(
    $false ),
    inference(simplify,[status(thm)],['61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7jk1weLEOg
% 0.14/0.38  % Computer   : n023.cluster.edu
% 0.14/0.38  % Model      : x86_64 x86_64
% 0.14/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.38  % Memory     : 8042.1875MB
% 0.14/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.38  % CPULimit   : 60
% 0.14/0.38  % DateTime   : Tue Dec  1 14:33:21 EST 2020
% 0.14/0.38  % CPUTime    : 
% 0.14/0.38  % Running portfolio for 600 s
% 0.14/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.49/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.49/0.67  % Solved by: fo/fo7.sh
% 0.49/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.67  % done 514 iterations in 0.215s
% 0.49/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.49/0.67  % SZS output start Refutation
% 0.49/0.67  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.49/0.67  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.49/0.67  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.49/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.49/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.49/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.49/0.67  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.49/0.67  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.49/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.67  thf(t100_xboole_1, conjecture,
% 0.49/0.67    (![A:$i,B:$i]:
% 0.49/0.67     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.49/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.67    (~( ![A:$i,B:$i]:
% 0.49/0.67        ( ( k4_xboole_0 @ A @ B ) =
% 0.49/0.67          ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.49/0.67    inference('cnf.neg', [status(esa)], [t100_xboole_1])).
% 0.49/0.67  thf('0', plain,
% 0.49/0.67      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.49/0.67         != (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf(commutativity_k3_xboole_0, axiom,
% 0.49/0.67    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.49/0.67  thf('1', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.49/0.67      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.49/0.67  thf('2', plain,
% 0.49/0.67      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.49/0.67         != (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.49/0.67      inference('demod', [status(thm)], ['0', '1'])).
% 0.49/0.67  thf('3', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.49/0.67      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.49/0.67  thf(t47_xboole_1, axiom,
% 0.49/0.67    (![A:$i,B:$i]:
% 0.49/0.67     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.49/0.67  thf('4', plain,
% 0.49/0.67      (![X14 : $i, X15 : $i]:
% 0.49/0.67         ((k4_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15))
% 0.49/0.67           = (k4_xboole_0 @ X14 @ X15))),
% 0.49/0.67      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.49/0.67  thf('5', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.49/0.67           = (k4_xboole_0 @ X0 @ X1))),
% 0.49/0.67      inference('sup+', [status(thm)], ['3', '4'])).
% 0.49/0.67  thf(d6_xboole_0, axiom,
% 0.49/0.67    (![A:$i,B:$i]:
% 0.49/0.67     ( ( k5_xboole_0 @ A @ B ) =
% 0.49/0.67       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.49/0.67  thf('6', plain,
% 0.49/0.67      (![X8 : $i, X9 : $i]:
% 0.49/0.67         ((k5_xboole_0 @ X8 @ X9)
% 0.49/0.67           = (k2_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ (k4_xboole_0 @ X9 @ X8)))),
% 0.49/0.67      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.49/0.67  thf('7', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 0.49/0.67           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 0.49/0.67              (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X1)))),
% 0.49/0.67      inference('sup+', [status(thm)], ['5', '6'])).
% 0.49/0.67  thf('8', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.49/0.67      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.49/0.67  thf(t48_xboole_1, axiom,
% 0.49/0.67    (![A:$i,B:$i]:
% 0.49/0.67     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.49/0.67  thf('9', plain,
% 0.49/0.67      (![X16 : $i, X17 : $i]:
% 0.49/0.67         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.49/0.67           = (k3_xboole_0 @ X16 @ X17))),
% 0.49/0.67      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.49/0.67  thf('10', plain,
% 0.49/0.67      (![X16 : $i, X17 : $i]:
% 0.49/0.67         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.49/0.67           = (k3_xboole_0 @ X16 @ X17))),
% 0.49/0.67      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.49/0.67  thf('11', plain,
% 0.49/0.67      (![X16 : $i, X17 : $i]:
% 0.49/0.67         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.49/0.67           = (k3_xboole_0 @ X16 @ X17))),
% 0.49/0.67      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.49/0.67  thf('12', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.49/0.67           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.49/0.67      inference('sup+', [status(thm)], ['10', '11'])).
% 0.49/0.67  thf('13', plain,
% 0.49/0.67      (![X14 : $i, X15 : $i]:
% 0.49/0.67         ((k4_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15))
% 0.49/0.67           = (k4_xboole_0 @ X14 @ X15))),
% 0.49/0.67      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.49/0.67  thf('14', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.49/0.67           = (k4_xboole_0 @ X1 @ X0))),
% 0.49/0.67      inference('sup+', [status(thm)], ['12', '13'])).
% 0.49/0.67  thf('15', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.49/0.67           = (k4_xboole_0 @ X0 @ X1))),
% 0.49/0.67      inference('sup+', [status(thm)], ['3', '4'])).
% 0.49/0.67  thf('16', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.49/0.67           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.49/0.67      inference('sup+', [status(thm)], ['14', '15'])).
% 0.49/0.67  thf(d5_xboole_0, axiom,
% 0.49/0.67    (![A:$i,B:$i,C:$i]:
% 0.49/0.67     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.49/0.67       ( ![D:$i]:
% 0.49/0.67         ( ( r2_hidden @ D @ C ) <=>
% 0.49/0.67           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.49/0.67  thf('17', plain,
% 0.49/0.67      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.49/0.67         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 0.49/0.67          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.49/0.67          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.49/0.67      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.49/0.67  thf('18', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.49/0.67          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.49/0.67      inference('eq_fact', [status(thm)], ['17'])).
% 0.49/0.67  thf(t5_boole, axiom,
% 0.49/0.67    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.49/0.67  thf('19', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.49/0.67      inference('cnf', [status(esa)], [t5_boole])).
% 0.49/0.67  thf(t1_xboole_0, axiom,
% 0.49/0.67    (![A:$i,B:$i,C:$i]:
% 0.49/0.67     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.49/0.67       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.49/0.67  thf('20', plain,
% 0.49/0.67      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.49/0.67         (~ (r2_hidden @ X10 @ X11)
% 0.49/0.67          | ~ (r2_hidden @ X10 @ X12)
% 0.49/0.67          | ~ (r2_hidden @ X10 @ (k5_xboole_0 @ X11 @ X12)))),
% 0.49/0.67      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.49/0.67  thf('21', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         (~ (r2_hidden @ X1 @ X0)
% 0.49/0.67          | ~ (r2_hidden @ X1 @ k1_xboole_0)
% 0.49/0.67          | ~ (r2_hidden @ X1 @ X0))),
% 0.49/0.67      inference('sup-', [status(thm)], ['19', '20'])).
% 0.49/0.67  thf('22', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.49/0.67      inference('simplify', [status(thm)], ['21'])).
% 0.49/0.67  thf('23', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.49/0.67      inference('condensation', [status(thm)], ['22'])).
% 0.49/0.67  thf('24', plain,
% 0.49/0.67      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.49/0.67      inference('sup-', [status(thm)], ['18', '23'])).
% 0.49/0.67  thf('25', plain,
% 0.49/0.67      (![X8 : $i, X9 : $i]:
% 0.49/0.67         ((k5_xboole_0 @ X8 @ X9)
% 0.49/0.67           = (k2_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ (k4_xboole_0 @ X9 @ X8)))),
% 0.49/0.67      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.49/0.67  thf('26', plain,
% 0.49/0.67      (![X0 : $i]:
% 0.49/0.67         ((k5_xboole_0 @ X0 @ k1_xboole_0)
% 0.49/0.67           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.49/0.67      inference('sup+', [status(thm)], ['24', '25'])).
% 0.49/0.67  thf('27', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.49/0.67      inference('cnf', [status(esa)], [t5_boole])).
% 0.49/0.67  thf('28', plain,
% 0.49/0.67      (![X0 : $i]:
% 0.49/0.67         ((X0) = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.49/0.67      inference('demod', [status(thm)], ['26', '27'])).
% 0.49/0.67  thf('29', plain,
% 0.49/0.67      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.49/0.67      inference('sup-', [status(thm)], ['18', '23'])).
% 0.49/0.67  thf(t98_xboole_1, axiom,
% 0.49/0.67    (![A:$i,B:$i]:
% 0.49/0.67     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.49/0.67  thf('30', plain,
% 0.49/0.67      (![X19 : $i, X20 : $i]:
% 0.49/0.67         ((k2_xboole_0 @ X19 @ X20)
% 0.49/0.67           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 0.49/0.67      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.49/0.67  thf('31', plain,
% 0.49/0.67      (![X0 : $i]:
% 0.49/0.67         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.49/0.67      inference('sup+', [status(thm)], ['29', '30'])).
% 0.49/0.67  thf('32', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.49/0.67      inference('cnf', [status(esa)], [t5_boole])).
% 0.49/0.67  thf('33', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.49/0.67      inference('sup+', [status(thm)], ['31', '32'])).
% 0.49/0.67  thf('34', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.49/0.67      inference('demod', [status(thm)], ['28', '33'])).
% 0.49/0.67  thf('35', plain,
% 0.49/0.67      (![X16 : $i, X17 : $i]:
% 0.49/0.67         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.49/0.67           = (k3_xboole_0 @ X16 @ X17))),
% 0.49/0.67      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.49/0.67  thf('36', plain,
% 0.49/0.67      (![X19 : $i, X20 : $i]:
% 0.49/0.67         ((k2_xboole_0 @ X19 @ X20)
% 0.49/0.67           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 0.49/0.67      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.49/0.67  thf('37', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 0.49/0.67           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.49/0.67      inference('sup+', [status(thm)], ['35', '36'])).
% 0.49/0.67  thf('38', plain,
% 0.49/0.67      (![X0 : $i]:
% 0.49/0.67         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ X0)
% 0.49/0.67           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.49/0.67      inference('sup+', [status(thm)], ['34', '37'])).
% 0.49/0.67  thf('39', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.49/0.67      inference('demod', [status(thm)], ['28', '33'])).
% 0.49/0.67  thf('40', plain,
% 0.49/0.67      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.49/0.67      inference('sup-', [status(thm)], ['18', '23'])).
% 0.49/0.67  thf('41', plain,
% 0.49/0.67      (![X16 : $i, X17 : $i]:
% 0.49/0.67         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.49/0.67           = (k3_xboole_0 @ X16 @ X17))),
% 0.49/0.67      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.49/0.67  thf('42', plain,
% 0.49/0.67      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.49/0.67      inference('sup+', [status(thm)], ['40', '41'])).
% 0.49/0.67  thf('43', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.49/0.67      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.49/0.67  thf('44', plain,
% 0.49/0.67      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.67      inference('sup+', [status(thm)], ['42', '43'])).
% 0.49/0.67  thf('45', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.49/0.67      inference('cnf', [status(esa)], [t5_boole])).
% 0.49/0.67  thf('46', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.49/0.67      inference('demod', [status(thm)], ['38', '39', '44', '45'])).
% 0.49/0.67  thf('47', plain,
% 0.49/0.67      (![X8 : $i, X9 : $i]:
% 0.49/0.67         ((k5_xboole_0 @ X8 @ X9)
% 0.49/0.67           = (k2_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ (k4_xboole_0 @ X9 @ X8)))),
% 0.49/0.67      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.49/0.67  thf('48', plain,
% 0.49/0.67      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.49/0.67      inference('sup+', [status(thm)], ['46', '47'])).
% 0.49/0.67  thf('49', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.49/0.67      inference('demod', [status(thm)], ['28', '33'])).
% 0.49/0.67  thf('50', plain,
% 0.49/0.67      (![X16 : $i, X17 : $i]:
% 0.49/0.67         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.49/0.67           = (k3_xboole_0 @ X16 @ X17))),
% 0.49/0.67      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.49/0.67  thf('51', plain,
% 0.49/0.67      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.49/0.67      inference('sup+', [status(thm)], ['49', '50'])).
% 0.49/0.67  thf('52', plain,
% 0.49/0.67      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.67      inference('sup+', [status(thm)], ['42', '43'])).
% 0.49/0.67  thf('53', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.49/0.67      inference('demod', [status(thm)], ['51', '52'])).
% 0.49/0.67  thf('54', plain,
% 0.49/0.67      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.49/0.67      inference('sup+', [status(thm)], ['46', '47'])).
% 0.49/0.67  thf('55', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.49/0.67      inference('demod', [status(thm)], ['53', '54'])).
% 0.49/0.67  thf('56', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((k1_xboole_0) = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.49/0.67      inference('demod', [status(thm)], ['16', '48', '55'])).
% 0.49/0.67  thf('57', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 0.49/0.67      inference('sup+', [status(thm)], ['9', '56'])).
% 0.49/0.67  thf('58', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.49/0.67      inference('sup+', [status(thm)], ['8', '57'])).
% 0.49/0.67  thf('59', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.49/0.67      inference('sup+', [status(thm)], ['31', '32'])).
% 0.49/0.67  thf('60', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 0.49/0.67           = (k4_xboole_0 @ X1 @ X0))),
% 0.49/0.67      inference('demod', [status(thm)], ['7', '58', '59'])).
% 0.49/0.67  thf('61', plain,
% 0.49/0.67      (((k4_xboole_0 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_A @ sk_B))),
% 0.49/0.67      inference('demod', [status(thm)], ['2', '60'])).
% 0.49/0.67  thf('62', plain, ($false), inference('simplify', [status(thm)], ['61'])).
% 0.49/0.67  
% 0.49/0.67  % SZS output end Refutation
% 0.49/0.67  
% 0.49/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
