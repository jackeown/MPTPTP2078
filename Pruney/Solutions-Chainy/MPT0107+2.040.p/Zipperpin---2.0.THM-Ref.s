%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DvxlXnCOvY

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:15 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   72 (  78 expanded)
%              Number of leaves         :   25 (  31 expanded)
%              Depth                    :   17
%              Number of atoms          :  456 ( 499 expanded)
%              Number of equality atoms :   53 (  58 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k2_xboole_0 @ X32 @ X33 )
      = ( k5_xboole_0 @ X32 @ ( k4_xboole_0 @ X33 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('4',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X23 @ X24 ) @ X24 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k4_xboole_0 @ X25 @ X26 )
        = X25 )
      | ~ ( r1_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

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
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('11',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('14',plain,(
    ! [X25: $i,X27: $i] :
      ( ( r1_xboole_0 @ X25 @ X27 )
      | ( ( k4_xboole_0 @ X25 @ X27 )
       != X25 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( X0 != X0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k4_xboole_0 @ X25 @ X26 )
        = X25 )
      | ~ ( r1_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k2_xboole_0 @ X32 @ X33 )
      = ( k5_xboole_0 @ X32 @ ( k4_xboole_0 @ X33 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('23',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('25',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['12','26'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('28',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( ( k4_xboole_0 @ X4 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('31',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['3','32'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('34',plain,(
    ! [X31: $i] :
      ( ( k5_xboole_0 @ X31 @ X31 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('35',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X28 @ X29 ) @ X30 )
      = ( k5_xboole_0 @ X28 @ ( k5_xboole_0 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('38',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','43'])).

thf('45',plain,(
    $false ),
    inference(simplify,[status(thm)],['44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DvxlXnCOvY
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 18:21:06 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.38/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.63  % Solved by: fo/fo7.sh
% 0.38/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.63  % done 482 iterations in 0.177s
% 0.38/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.63  % SZS output start Refutation
% 0.38/0.63  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.38/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.63  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.38/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.63  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.63  thf(t100_xboole_1, conjecture,
% 0.38/0.63    (![A:$i,B:$i]:
% 0.38/0.63     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.38/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.63    (~( ![A:$i,B:$i]:
% 0.38/0.63        ( ( k4_xboole_0 @ A @ B ) =
% 0.38/0.63          ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.38/0.63    inference('cnf.neg', [status(esa)], [t100_xboole_1])).
% 0.38/0.63  thf('0', plain,
% 0.38/0.63      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.38/0.63         != (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf(t47_xboole_1, axiom,
% 0.38/0.63    (![A:$i,B:$i]:
% 0.38/0.63     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.38/0.63  thf('1', plain,
% 0.38/0.63      (![X15 : $i, X16 : $i]:
% 0.38/0.63         ((k4_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16))
% 0.38/0.63           = (k4_xboole_0 @ X15 @ X16))),
% 0.38/0.63      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.38/0.63  thf(t98_xboole_1, axiom,
% 0.38/0.63    (![A:$i,B:$i]:
% 0.38/0.63     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.38/0.63  thf('2', plain,
% 0.38/0.63      (![X32 : $i, X33 : $i]:
% 0.38/0.63         ((k2_xboole_0 @ X32 @ X33)
% 0.38/0.63           = (k5_xboole_0 @ X32 @ (k4_xboole_0 @ X33 @ X32)))),
% 0.38/0.63      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.38/0.63  thf('3', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]:
% 0.38/0.63         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 0.38/0.63           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.38/0.63      inference('sup+', [status(thm)], ['1', '2'])).
% 0.38/0.63  thf(t79_xboole_1, axiom,
% 0.38/0.63    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.38/0.63  thf('4', plain,
% 0.38/0.63      (![X23 : $i, X24 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X23 @ X24) @ X24)),
% 0.38/0.63      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.38/0.63  thf(symmetry_r1_xboole_0, axiom,
% 0.38/0.63    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.38/0.63  thf('5', plain,
% 0.38/0.63      (![X2 : $i, X3 : $i]:
% 0.38/0.63         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.38/0.63      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.38/0.63  thf('6', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.38/0.63      inference('sup-', [status(thm)], ['4', '5'])).
% 0.38/0.63  thf(t83_xboole_1, axiom,
% 0.38/0.63    (![A:$i,B:$i]:
% 0.38/0.63     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.38/0.63  thf('7', plain,
% 0.38/0.63      (![X25 : $i, X26 : $i]:
% 0.38/0.63         (((k4_xboole_0 @ X25 @ X26) = (X25)) | ~ (r1_xboole_0 @ X25 @ X26))),
% 0.38/0.63      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.38/0.63  thf('8', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]:
% 0.38/0.63         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.38/0.63      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.63  thf(t48_xboole_1, axiom,
% 0.38/0.63    (![A:$i,B:$i]:
% 0.38/0.63     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.38/0.63  thf('9', plain,
% 0.38/0.63      (![X17 : $i, X18 : $i]:
% 0.38/0.63         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.38/0.63           = (k3_xboole_0 @ X17 @ X18))),
% 0.38/0.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.63  thf('10', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]:
% 0.38/0.63         ((k4_xboole_0 @ X0 @ X0)
% 0.38/0.63           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.38/0.63      inference('sup+', [status(thm)], ['8', '9'])).
% 0.38/0.63  thf(t49_xboole_1, axiom,
% 0.38/0.63    (![A:$i,B:$i,C:$i]:
% 0.38/0.63     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.38/0.63       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.38/0.63  thf('11', plain,
% 0.38/0.63      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.38/0.63         ((k3_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 0.38/0.63           = (k4_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ X21))),
% 0.38/0.63      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.38/0.63  thf('12', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]:
% 0.38/0.63         ((k4_xboole_0 @ X0 @ X0)
% 0.38/0.63           = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.38/0.63      inference('demod', [status(thm)], ['10', '11'])).
% 0.38/0.63  thf(t3_boole, axiom,
% 0.38/0.63    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.38/0.63  thf('13', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.38/0.63      inference('cnf', [status(esa)], [t3_boole])).
% 0.38/0.63  thf('14', plain,
% 0.38/0.63      (![X25 : $i, X27 : $i]:
% 0.38/0.63         ((r1_xboole_0 @ X25 @ X27) | ((k4_xboole_0 @ X25 @ X27) != (X25)))),
% 0.38/0.63      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.38/0.63  thf('15', plain,
% 0.38/0.63      (![X0 : $i]: (((X0) != (X0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.38/0.63      inference('sup-', [status(thm)], ['13', '14'])).
% 0.38/0.63  thf('16', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.38/0.63      inference('simplify', [status(thm)], ['15'])).
% 0.38/0.63  thf('17', plain,
% 0.38/0.63      (![X2 : $i, X3 : $i]:
% 0.38/0.63         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.38/0.63      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.38/0.63  thf('18', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.38/0.63      inference('sup-', [status(thm)], ['16', '17'])).
% 0.38/0.63  thf('19', plain,
% 0.38/0.63      (![X25 : $i, X26 : $i]:
% 0.38/0.63         (((k4_xboole_0 @ X25 @ X26) = (X25)) | ~ (r1_xboole_0 @ X25 @ X26))),
% 0.38/0.63      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.38/0.63  thf('20', plain,
% 0.38/0.63      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.38/0.63      inference('sup-', [status(thm)], ['18', '19'])).
% 0.38/0.63  thf('21', plain,
% 0.38/0.63      (![X32 : $i, X33 : $i]:
% 0.38/0.63         ((k2_xboole_0 @ X32 @ X33)
% 0.38/0.63           = (k5_xboole_0 @ X32 @ (k4_xboole_0 @ X33 @ X32)))),
% 0.38/0.63      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.38/0.63  thf('22', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.38/0.63      inference('sup+', [status(thm)], ['20', '21'])).
% 0.38/0.63  thf(t5_boole, axiom,
% 0.38/0.63    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.38/0.63  thf('23', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.38/0.63      inference('cnf', [status(esa)], [t5_boole])).
% 0.38/0.63  thf('24', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.38/0.63      inference('sup+', [status(thm)], ['22', '23'])).
% 0.38/0.63  thf(t46_xboole_1, axiom,
% 0.38/0.63    (![A:$i,B:$i]:
% 0.38/0.63     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.38/0.63  thf('25', plain,
% 0.38/0.63      (![X13 : $i, X14 : $i]:
% 0.38/0.63         ((k4_xboole_0 @ X13 @ (k2_xboole_0 @ X13 @ X14)) = (k1_xboole_0))),
% 0.38/0.63      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.38/0.63  thf('26', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.38/0.63      inference('sup+', [status(thm)], ['24', '25'])).
% 0.38/0.63  thf('27', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]:
% 0.38/0.63         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.38/0.63      inference('demod', [status(thm)], ['12', '26'])).
% 0.38/0.63  thf(l32_xboole_1, axiom,
% 0.38/0.63    (![A:$i,B:$i]:
% 0.38/0.63     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.63  thf('28', plain,
% 0.38/0.63      (![X4 : $i, X5 : $i]:
% 0.38/0.63         ((r1_tarski @ X4 @ X5) | ((k4_xboole_0 @ X4 @ X5) != (k1_xboole_0)))),
% 0.38/0.63      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.38/0.63  thf('29', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]:
% 0.38/0.63         (((k1_xboole_0) != (k1_xboole_0))
% 0.38/0.63          | (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.38/0.63      inference('sup-', [status(thm)], ['27', '28'])).
% 0.38/0.63  thf('30', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.38/0.63      inference('simplify', [status(thm)], ['29'])).
% 0.38/0.63  thf(t12_xboole_1, axiom,
% 0.38/0.63    (![A:$i,B:$i]:
% 0.38/0.63     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.38/0.63  thf('31', plain,
% 0.38/0.63      (![X7 : $i, X8 : $i]:
% 0.38/0.63         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.38/0.63      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.38/0.63  thf('32', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]:
% 0.38/0.63         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.38/0.63      inference('sup-', [status(thm)], ['30', '31'])).
% 0.38/0.63  thf('33', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]:
% 0.38/0.63         ((X1)
% 0.38/0.63           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.38/0.63      inference('demod', [status(thm)], ['3', '32'])).
% 0.38/0.63  thf(t92_xboole_1, axiom,
% 0.38/0.63    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.38/0.63  thf('34', plain, (![X31 : $i]: ((k5_xboole_0 @ X31 @ X31) = (k1_xboole_0))),
% 0.38/0.63      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.38/0.63  thf(t91_xboole_1, axiom,
% 0.38/0.63    (![A:$i,B:$i,C:$i]:
% 0.38/0.63     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.38/0.63       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.38/0.63  thf('35', plain,
% 0.38/0.63      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.38/0.63         ((k5_xboole_0 @ (k5_xboole_0 @ X28 @ X29) @ X30)
% 0.38/0.63           = (k5_xboole_0 @ X28 @ (k5_xboole_0 @ X29 @ X30)))),
% 0.38/0.63      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.38/0.63  thf('36', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]:
% 0.38/0.63         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.38/0.63           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.38/0.63      inference('sup+', [status(thm)], ['34', '35'])).
% 0.38/0.63  thf(commutativity_k5_xboole_0, axiom,
% 0.38/0.63    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.38/0.63  thf('37', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.38/0.63      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.38/0.63  thf('38', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.38/0.63      inference('cnf', [status(esa)], [t5_boole])).
% 0.38/0.63  thf('39', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.38/0.63      inference('sup+', [status(thm)], ['37', '38'])).
% 0.38/0.63  thf('40', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]:
% 0.38/0.63         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.38/0.63      inference('demod', [status(thm)], ['36', '39'])).
% 0.38/0.63  thf('41', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]:
% 0.38/0.63         ((k4_xboole_0 @ X0 @ X1)
% 0.38/0.63           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.38/0.63      inference('sup+', [status(thm)], ['33', '40'])).
% 0.38/0.63  thf('42', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.38/0.63      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.38/0.63  thf('43', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]:
% 0.38/0.63         ((k4_xboole_0 @ X0 @ X1)
% 0.38/0.63           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.38/0.63      inference('demod', [status(thm)], ['41', '42'])).
% 0.38/0.63  thf('44', plain,
% 0.38/0.63      (((k4_xboole_0 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_A @ sk_B))),
% 0.38/0.63      inference('demod', [status(thm)], ['0', '43'])).
% 0.38/0.63  thf('45', plain, ($false), inference('simplify', [status(thm)], ['44'])).
% 0.38/0.63  
% 0.38/0.63  % SZS output end Refutation
% 0.38/0.63  
% 0.48/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
