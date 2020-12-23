%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Kpqr74UhMW

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:13 EST 2020

% Result     : Theorem 0.79s
% Output     : Refutation 0.79s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 156 expanded)
%              Number of leaves         :   18 (  55 expanded)
%              Depth                    :   13
%              Number of atoms          :  512 (1190 expanded)
%              Number of equality atoms :   58 ( 128 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
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

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('8',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

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
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('19',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('20',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['21'])).

thf('25',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('32',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('35',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('45',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k4_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','39','40','49'])).

thf('51',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','50'])).

thf('52',plain,(
    $false ),
    inference(simplify,[status(thm)],['51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Kpqr74UhMW
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:13:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.79/0.98  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.79/0.98  % Solved by: fo/fo7.sh
% 0.79/0.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.79/0.98  % done 1056 iterations in 0.531s
% 0.79/0.98  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.79/0.98  % SZS output start Refutation
% 0.79/0.98  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.79/0.98  thf(sk_B_type, type, sk_B: $i).
% 0.79/0.98  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.79/0.98  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.79/0.98  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.79/0.98  thf(sk_A_type, type, sk_A: $i).
% 0.79/0.98  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.79/0.98  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.79/0.98  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.79/0.98  thf(t100_xboole_1, conjecture,
% 0.79/0.98    (![A:$i,B:$i]:
% 0.79/0.98     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.79/0.98  thf(zf_stmt_0, negated_conjecture,
% 0.79/0.98    (~( ![A:$i,B:$i]:
% 0.79/0.98        ( ( k4_xboole_0 @ A @ B ) =
% 0.79/0.98          ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.79/0.98    inference('cnf.neg', [status(esa)], [t100_xboole_1])).
% 0.79/0.98  thf('0', plain,
% 0.79/0.98      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.79/0.98         != (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.79/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.98  thf(commutativity_k3_xboole_0, axiom,
% 0.79/0.98    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.79/0.98  thf('1', plain,
% 0.79/0.98      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.79/0.98      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.79/0.98  thf('2', plain,
% 0.79/0.98      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.79/0.98         != (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.79/0.98      inference('demod', [status(thm)], ['0', '1'])).
% 0.79/0.98  thf('3', plain,
% 0.79/0.98      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.79/0.98      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.79/0.98  thf(t47_xboole_1, axiom,
% 0.79/0.98    (![A:$i,B:$i]:
% 0.79/0.98     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.79/0.98  thf('4', plain,
% 0.79/0.98      (![X11 : $i, X12 : $i]:
% 0.79/0.98         ((k4_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12))
% 0.79/0.98           = (k4_xboole_0 @ X11 @ X12))),
% 0.79/0.98      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.79/0.98  thf('5', plain,
% 0.79/0.98      (![X0 : $i, X1 : $i]:
% 0.79/0.98         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.79/0.98           = (k4_xboole_0 @ X0 @ X1))),
% 0.79/0.98      inference('sup+', [status(thm)], ['3', '4'])).
% 0.79/0.98  thf(d6_xboole_0, axiom,
% 0.79/0.98    (![A:$i,B:$i]:
% 0.79/0.98     ( ( k5_xboole_0 @ A @ B ) =
% 0.79/0.98       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.79/0.98  thf('6', plain,
% 0.79/0.98      (![X8 : $i, X9 : $i]:
% 0.79/0.98         ((k5_xboole_0 @ X8 @ X9)
% 0.79/0.98           = (k2_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ (k4_xboole_0 @ X9 @ X8)))),
% 0.79/0.98      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.79/0.98  thf('7', plain,
% 0.79/0.98      (![X0 : $i, X1 : $i]:
% 0.79/0.98         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 0.79/0.98           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 0.79/0.98              (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X1)))),
% 0.79/0.98      inference('sup+', [status(thm)], ['5', '6'])).
% 0.79/0.98  thf(t49_xboole_1, axiom,
% 0.79/0.98    (![A:$i,B:$i,C:$i]:
% 0.79/0.98     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.79/0.98       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.79/0.98  thf('8', plain,
% 0.79/0.98      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.79/0.98         ((k3_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X17))
% 0.79/0.98           = (k4_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ X17))),
% 0.79/0.98      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.79/0.98  thf('9', plain,
% 0.79/0.98      (![X0 : $i, X1 : $i]:
% 0.79/0.98         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 0.79/0.98           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 0.79/0.98              (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X1))))),
% 0.79/0.98      inference('demod', [status(thm)], ['7', '8'])).
% 0.79/0.98  thf('10', plain,
% 0.79/0.98      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.79/0.98         ((k3_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X17))
% 0.79/0.98           = (k4_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ X17))),
% 0.79/0.98      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.79/0.98  thf(t3_boole, axiom,
% 0.79/0.98    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.79/0.98  thf('11', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.79/0.98      inference('cnf', [status(esa)], [t3_boole])).
% 0.79/0.98  thf(t48_xboole_1, axiom,
% 0.79/0.98    (![A:$i,B:$i]:
% 0.79/0.98     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.79/0.98  thf('12', plain,
% 0.79/0.98      (![X13 : $i, X14 : $i]:
% 0.79/0.98         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.79/0.98           = (k3_xboole_0 @ X13 @ X14))),
% 0.79/0.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.79/0.98  thf('13', plain,
% 0.79/0.98      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.79/0.98      inference('sup+', [status(thm)], ['11', '12'])).
% 0.79/0.98  thf('14', plain,
% 0.79/0.98      (![X0 : $i, X1 : $i]:
% 0.79/0.98         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 0.79/0.98           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 0.79/0.98      inference('sup+', [status(thm)], ['10', '13'])).
% 0.79/0.98  thf('15', plain,
% 0.79/0.98      (![X0 : $i, X1 : $i]:
% 0.79/0.98         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.79/0.98           = (k4_xboole_0 @ X0 @ X1))),
% 0.79/0.98      inference('sup+', [status(thm)], ['3', '4'])).
% 0.79/0.98  thf('16', plain,
% 0.79/0.98      (![X0 : $i, X1 : $i]:
% 0.79/0.98         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1))
% 0.79/0.98           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 0.79/0.98      inference('demod', [status(thm)], ['14', '15'])).
% 0.79/0.98  thf(d5_xboole_0, axiom,
% 0.79/0.98    (![A:$i,B:$i,C:$i]:
% 0.79/0.98     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.79/0.98       ( ![D:$i]:
% 0.79/0.98         ( ( r2_hidden @ D @ C ) <=>
% 0.79/0.98           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.79/0.98  thf('17', plain,
% 0.79/0.98      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.79/0.98         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 0.79/0.98          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.79/0.98          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.79/0.98      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.79/0.98  thf('18', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.79/0.98      inference('cnf', [status(esa)], [t3_boole])).
% 0.79/0.98  thf('19', plain,
% 0.79/0.98      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.79/0.98         (~ (r2_hidden @ X6 @ X5)
% 0.79/0.98          | ~ (r2_hidden @ X6 @ X4)
% 0.79/0.98          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.79/0.98      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.79/0.98  thf('20', plain,
% 0.79/0.98      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.79/0.98         (~ (r2_hidden @ X6 @ X4)
% 0.79/0.98          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.79/0.98      inference('simplify', [status(thm)], ['19'])).
% 0.79/0.98  thf('21', plain,
% 0.79/0.98      (![X0 : $i, X1 : $i]:
% 0.79/0.98         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.79/0.98      inference('sup-', [status(thm)], ['18', '20'])).
% 0.79/0.98  thf('22', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.79/0.98      inference('condensation', [status(thm)], ['21'])).
% 0.79/0.98  thf('23', plain,
% 0.79/0.98      (![X0 : $i, X1 : $i]:
% 0.79/0.98         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.79/0.98          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.79/0.98      inference('sup-', [status(thm)], ['17', '22'])).
% 0.79/0.98  thf('24', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.79/0.98      inference('condensation', [status(thm)], ['21'])).
% 0.79/0.98  thf('25', plain,
% 0.79/0.98      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.79/0.98      inference('sup-', [status(thm)], ['23', '24'])).
% 0.79/0.98  thf('26', plain,
% 0.79/0.98      (![X13 : $i, X14 : $i]:
% 0.79/0.98         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.79/0.98           = (k3_xboole_0 @ X13 @ X14))),
% 0.79/0.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.79/0.98  thf('27', plain,
% 0.79/0.98      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.79/0.98      inference('sup+', [status(thm)], ['25', '26'])).
% 0.79/0.98  thf('28', plain,
% 0.79/0.98      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.79/0.98      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.79/0.98  thf('29', plain,
% 0.79/0.98      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.79/0.98      inference('sup+', [status(thm)], ['27', '28'])).
% 0.79/0.98  thf('30', plain,
% 0.79/0.98      (![X0 : $i, X1 : $i]:
% 0.79/0.98         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.79/0.98      inference('demod', [status(thm)], ['16', '29'])).
% 0.79/0.98  thf('31', plain,
% 0.79/0.98      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.79/0.98      inference('sup+', [status(thm)], ['11', '12'])).
% 0.79/0.98  thf('32', plain,
% 0.79/0.98      (![X11 : $i, X12 : $i]:
% 0.79/0.98         ((k4_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12))
% 0.79/0.98           = (k4_xboole_0 @ X11 @ X12))),
% 0.79/0.98      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.79/0.98  thf('33', plain,
% 0.79/0.98      (![X0 : $i]:
% 0.79/0.98         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0))
% 0.79/0.98           = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.79/0.98      inference('sup+', [status(thm)], ['31', '32'])).
% 0.79/0.98  thf('34', plain,
% 0.79/0.98      (![X13 : $i, X14 : $i]:
% 0.79/0.98         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.79/0.98           = (k3_xboole_0 @ X13 @ X14))),
% 0.79/0.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.79/0.98  thf('35', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.79/0.98      inference('cnf', [status(esa)], [t3_boole])).
% 0.79/0.98  thf('36', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.79/0.98      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.79/0.98  thf('37', plain,
% 0.79/0.98      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.79/0.98         ((k3_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X17))
% 0.79/0.98           = (k4_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ X17))),
% 0.79/0.98      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.79/0.98  thf('38', plain,
% 0.79/0.98      (![X0 : $i, X1 : $i]:
% 0.79/0.98         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.79/0.98           = (k4_xboole_0 @ X0 @ X1))),
% 0.79/0.98      inference('sup+', [status(thm)], ['36', '37'])).
% 0.79/0.98  thf('39', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.79/0.98      inference('sup+', [status(thm)], ['30', '38'])).
% 0.79/0.98  thf('40', plain,
% 0.79/0.98      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.79/0.98      inference('sup+', [status(thm)], ['27', '28'])).
% 0.79/0.98  thf('41', plain,
% 0.79/0.98      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.79/0.98      inference('sup+', [status(thm)], ['11', '12'])).
% 0.79/0.98  thf('42', plain,
% 0.79/0.98      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.79/0.98      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.79/0.98  thf('43', plain,
% 0.79/0.98      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.79/0.98      inference('sup+', [status(thm)], ['41', '42'])).
% 0.79/0.98  thf('44', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.79/0.98      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.79/0.98  thf(t51_xboole_1, axiom,
% 0.79/0.98    (![A:$i,B:$i]:
% 0.79/0.98     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.79/0.98       ( A ) ))).
% 0.79/0.98  thf('45', plain,
% 0.79/0.98      (![X18 : $i, X19 : $i]:
% 0.79/0.98         ((k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ (k4_xboole_0 @ X18 @ X19))
% 0.79/0.98           = (X18))),
% 0.79/0.98      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.79/0.98  thf('46', plain,
% 0.79/0.98      (![X0 : $i]: ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)) = (X0))),
% 0.79/0.98      inference('sup+', [status(thm)], ['44', '45'])).
% 0.79/0.98  thf('47', plain,
% 0.79/0.98      (![X0 : $i]:
% 0.79/0.98         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)) = (X0))),
% 0.79/0.98      inference('sup+', [status(thm)], ['43', '46'])).
% 0.79/0.98  thf('48', plain,
% 0.79/0.98      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.79/0.98      inference('sup+', [status(thm)], ['25', '26'])).
% 0.79/0.98  thf('49', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.79/0.98      inference('demod', [status(thm)], ['47', '48'])).
% 0.79/0.98  thf('50', plain,
% 0.79/0.98      (![X0 : $i, X1 : $i]:
% 0.79/0.98         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 0.79/0.98           = (k4_xboole_0 @ X1 @ X0))),
% 0.79/0.98      inference('demod', [status(thm)], ['9', '39', '40', '49'])).
% 0.79/0.98  thf('51', plain,
% 0.79/0.98      (((k4_xboole_0 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_A @ sk_B))),
% 0.79/0.98      inference('demod', [status(thm)], ['2', '50'])).
% 0.79/0.98  thf('52', plain, ($false), inference('simplify', [status(thm)], ['51'])).
% 0.79/0.98  
% 0.79/0.98  % SZS output end Refutation
% 0.79/0.98  
% 0.79/0.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
