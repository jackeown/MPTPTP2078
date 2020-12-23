%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7EnAiG2pud

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:34 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :   67 (  89 expanded)
%              Number of leaves         :   19 (  36 expanded)
%              Depth                    :   16
%              Number of atoms          :  491 ( 671 expanded)
%              Number of equality atoms :   47 (  63 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t81_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
       => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t81_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('4',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X2 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('7',plain,(
    r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('14',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','12','21'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
      = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('26',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ X0 @ sk_C ) ) ) ) ),
    inference('sup+',[status(thm)],['6','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C ) ) ) ) ),
    inference('sup+',[status(thm)],['5','27'])).

thf('29',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('30',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup+',[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('36',plain,
    ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('38',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('42',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['36','37','40','41'])).

thf('43',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('44',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['0','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7EnAiG2pud
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:39:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.58/0.79  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.58/0.79  % Solved by: fo/fo7.sh
% 0.58/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.79  % done 704 iterations in 0.350s
% 0.58/0.79  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.58/0.79  % SZS output start Refutation
% 0.58/0.79  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.58/0.79  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.79  thf(sk_C_type, type, sk_C: $i).
% 0.58/0.79  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.58/0.79  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.58/0.79  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.58/0.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.79  thf(t81_xboole_1, conjecture,
% 0.58/0.79    (![A:$i,B:$i,C:$i]:
% 0.58/0.79     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.58/0.79       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.58/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.79    (~( ![A:$i,B:$i,C:$i]:
% 0.58/0.79        ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.58/0.79          ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )),
% 0.58/0.79    inference('cnf.neg', [status(esa)], [t81_xboole_1])).
% 0.58/0.79  thf('0', plain, (~ (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf(t48_xboole_1, axiom,
% 0.58/0.79    (![A:$i,B:$i]:
% 0.58/0.79     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.58/0.79  thf('1', plain,
% 0.58/0.79      (![X16 : $i, X17 : $i]:
% 0.58/0.79         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.58/0.79           = (k3_xboole_0 @ X16 @ X17))),
% 0.58/0.79      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.58/0.79  thf(t41_xboole_1, axiom,
% 0.58/0.79    (![A:$i,B:$i,C:$i]:
% 0.58/0.79     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.58/0.79       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.58/0.79  thf('2', plain,
% 0.58/0.79      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.58/0.79         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 0.58/0.79           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.58/0.79      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.58/0.79  thf('3', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.79         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.58/0.79           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 0.58/0.79      inference('sup+', [status(thm)], ['1', '2'])).
% 0.58/0.79  thf(t49_xboole_1, axiom,
% 0.58/0.79    (![A:$i,B:$i,C:$i]:
% 0.58/0.79     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.58/0.79       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.58/0.79  thf('4', plain,
% 0.58/0.79      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.58/0.79         ((k3_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 0.58/0.79           = (k4_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X20))),
% 0.58/0.79      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.58/0.79  thf('5', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.79         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X2))
% 0.58/0.79           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 0.58/0.79      inference('demod', [status(thm)], ['3', '4'])).
% 0.58/0.79  thf(commutativity_k2_xboole_0, axiom,
% 0.58/0.79    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.58/0.79  thf('6', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.58/0.79      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.58/0.79  thf('7', plain, ((r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf(d7_xboole_0, axiom,
% 0.58/0.79    (![A:$i,B:$i]:
% 0.58/0.79     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.58/0.79       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.58/0.79  thf('8', plain,
% 0.58/0.79      (![X2 : $i, X3 : $i]:
% 0.58/0.79         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.58/0.79      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.58/0.79  thf('9', plain,
% 0.58/0.79      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 0.58/0.79      inference('sup-', [status(thm)], ['7', '8'])).
% 0.58/0.79  thf('10', plain,
% 0.58/0.79      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.58/0.79         ((k3_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 0.58/0.79           = (k4_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X20))),
% 0.58/0.79      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.58/0.79  thf('11', plain,
% 0.58/0.79      (![X0 : $i]:
% 0.58/0.79         ((k3_xboole_0 @ sk_A @ 
% 0.58/0.79           (k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ X0))
% 0.58/0.79           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.58/0.79      inference('sup+', [status(thm)], ['9', '10'])).
% 0.58/0.79  thf('12', plain,
% 0.58/0.79      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.58/0.79         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 0.58/0.79           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.58/0.79      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.58/0.79  thf(t3_boole, axiom,
% 0.58/0.79    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.58/0.79  thf('13', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.58/0.79      inference('cnf', [status(esa)], [t3_boole])).
% 0.58/0.79  thf(t36_xboole_1, axiom,
% 0.58/0.79    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.58/0.79  thf('14', plain,
% 0.58/0.79      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 0.58/0.79      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.58/0.79  thf('15', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.58/0.79      inference('sup+', [status(thm)], ['13', '14'])).
% 0.58/0.79  thf(l32_xboole_1, axiom,
% 0.58/0.79    (![A:$i,B:$i]:
% 0.58/0.79     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.58/0.79  thf('16', plain,
% 0.58/0.79      (![X5 : $i, X7 : $i]:
% 0.58/0.79         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.58/0.79      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.58/0.79  thf('17', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.58/0.79      inference('sup-', [status(thm)], ['15', '16'])).
% 0.58/0.79  thf('18', plain,
% 0.58/0.79      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 0.58/0.79      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.58/0.79  thf('19', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.58/0.79      inference('sup+', [status(thm)], ['17', '18'])).
% 0.58/0.79  thf('20', plain,
% 0.58/0.79      (![X5 : $i, X7 : $i]:
% 0.58/0.79         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.58/0.79      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.58/0.79  thf('21', plain,
% 0.58/0.79      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.58/0.79      inference('sup-', [status(thm)], ['19', '20'])).
% 0.58/0.79  thf('22', plain,
% 0.58/0.79      (![X0 : $i]:
% 0.58/0.79         ((k3_xboole_0 @ sk_A @ 
% 0.58/0.79           (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C @ X0))) = (k1_xboole_0))),
% 0.58/0.79      inference('demod', [status(thm)], ['11', '12', '21'])).
% 0.58/0.79  thf(t47_xboole_1, axiom,
% 0.58/0.79    (![A:$i,B:$i]:
% 0.58/0.79     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.58/0.79  thf('23', plain,
% 0.58/0.79      (![X14 : $i, X15 : $i]:
% 0.58/0.79         ((k4_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15))
% 0.58/0.79           = (k4_xboole_0 @ X14 @ X15))),
% 0.58/0.79      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.58/0.79  thf('24', plain,
% 0.58/0.79      (![X0 : $i]:
% 0.58/0.79         ((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.58/0.79           = (k4_xboole_0 @ sk_A @ 
% 0.58/0.79              (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C @ X0))))),
% 0.58/0.79      inference('sup+', [status(thm)], ['22', '23'])).
% 0.58/0.79  thf('25', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.58/0.79      inference('cnf', [status(esa)], [t3_boole])).
% 0.58/0.79  thf('26', plain,
% 0.58/0.79      (![X0 : $i]:
% 0.58/0.79         ((sk_A)
% 0.58/0.79           = (k4_xboole_0 @ sk_A @ 
% 0.58/0.79              (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C @ X0))))),
% 0.58/0.79      inference('demod', [status(thm)], ['24', '25'])).
% 0.58/0.79  thf('27', plain,
% 0.58/0.79      (![X0 : $i]:
% 0.58/0.79         ((sk_A)
% 0.58/0.79           = (k4_xboole_0 @ sk_A @ 
% 0.58/0.79              (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ X0 @ sk_C))))),
% 0.58/0.79      inference('sup+', [status(thm)], ['6', '26'])).
% 0.58/0.79  thf('28', plain,
% 0.58/0.79      (![X0 : $i]:
% 0.58/0.79         ((sk_A)
% 0.58/0.79           = (k4_xboole_0 @ sk_A @ 
% 0.58/0.79              (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_C))))),
% 0.58/0.79      inference('sup+', [status(thm)], ['5', '27'])).
% 0.58/0.79  thf('29', plain,
% 0.58/0.79      (![X16 : $i, X17 : $i]:
% 0.58/0.79         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.58/0.79           = (k3_xboole_0 @ X16 @ X17))),
% 0.58/0.79      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.58/0.79  thf('30', plain,
% 0.58/0.79      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.58/0.79         ((k3_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 0.58/0.79           = (k4_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X20))),
% 0.58/0.79      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.58/0.79  thf('31', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.79         ((k3_xboole_0 @ X2 @ 
% 0.58/0.79           (k4_xboole_0 @ X1 @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)))
% 0.58/0.79           = (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 0.58/0.79      inference('sup+', [status(thm)], ['29', '30'])).
% 0.58/0.79  thf('32', plain,
% 0.58/0.79      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.58/0.79         ((k3_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 0.58/0.79           = (k4_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X20))),
% 0.58/0.79      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.58/0.79  thf('33', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.79         ((k3_xboole_0 @ X2 @ 
% 0.58/0.79           (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))
% 0.58/0.79           = (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 0.58/0.79      inference('demod', [status(thm)], ['31', '32'])).
% 0.58/0.79  thf('34', plain,
% 0.58/0.79      (((k3_xboole_0 @ sk_B @ sk_A)
% 0.58/0.79         = (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_C))),
% 0.58/0.79      inference('sup+', [status(thm)], ['28', '33'])).
% 0.58/0.79  thf('35', plain,
% 0.58/0.79      (![X14 : $i, X15 : $i]:
% 0.58/0.79         ((k4_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15))
% 0.58/0.79           = (k4_xboole_0 @ X14 @ X15))),
% 0.58/0.79      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.58/0.79  thf('36', plain,
% 0.58/0.79      (((k4_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ 
% 0.58/0.79         (k3_xboole_0 @ sk_B @ sk_A))
% 0.58/0.79         = (k4_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_C))),
% 0.58/0.79      inference('sup+', [status(thm)], ['34', '35'])).
% 0.58/0.79  thf('37', plain,
% 0.58/0.79      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.58/0.79         ((k3_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 0.58/0.79           = (k4_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X20))),
% 0.58/0.79      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.58/0.79  thf('38', plain,
% 0.58/0.79      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.58/0.79         ((k3_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 0.58/0.79           = (k4_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X20))),
% 0.58/0.79      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.58/0.79  thf('39', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.58/0.79      inference('sup-', [status(thm)], ['15', '16'])).
% 0.58/0.79  thf('40', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 0.58/0.79           = (k1_xboole_0))),
% 0.58/0.79      inference('sup+', [status(thm)], ['38', '39'])).
% 0.58/0.79  thf('41', plain,
% 0.58/0.79      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.58/0.79         ((k3_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 0.58/0.79           = (k4_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X20))),
% 0.58/0.79      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.58/0.79  thf('42', plain,
% 0.58/0.79      (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 0.58/0.79      inference('demod', [status(thm)], ['36', '37', '40', '41'])).
% 0.58/0.79  thf('43', plain,
% 0.58/0.79      (![X2 : $i, X4 : $i]:
% 0.58/0.79         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.58/0.79      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.58/0.79  thf('44', plain,
% 0.58/0.79      ((((k1_xboole_0) != (k1_xboole_0))
% 0.58/0.79        | (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['42', '43'])).
% 0.58/0.79  thf('45', plain, ((r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 0.58/0.79      inference('simplify', [status(thm)], ['44'])).
% 0.58/0.79  thf('46', plain, ($false), inference('demod', [status(thm)], ['0', '45'])).
% 0.58/0.79  
% 0.58/0.79  % SZS output end Refutation
% 0.58/0.79  
% 0.58/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
