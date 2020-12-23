%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.H63ih96x1w

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:22 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 110 expanded)
%              Number of leaves         :   23 (  43 expanded)
%              Depth                    :   17
%              Number of atoms          :  451 ( 712 expanded)
%              Number of equality atoms :   56 (  94 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t14_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t14_zfmisc_1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X48: $i,X49: $i] :
      ( r1_tarski @ ( k1_tarski @ X48 ) @ ( k2_tarski @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_tarski @ X1 ) ) ),
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

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('7',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('8',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('10',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('20',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('24',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['22','25'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('30',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','37'])).

thf('39',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['13','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['6','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k4_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k1_tarski @ X0 ) ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','42'])).

thf('44',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','45'])).

thf('47',plain,(
    $false ),
    inference(simplify,[status(thm)],['46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.H63ih96x1w
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:47:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.48/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.48/0.68  % Solved by: fo/fo7.sh
% 0.48/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.68  % done 545 iterations in 0.227s
% 0.48/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.48/0.68  % SZS output start Refutation
% 0.48/0.68  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.48/0.68  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.48/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.48/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.48/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.48/0.68  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.48/0.68  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.48/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.48/0.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.48/0.68  thf(t14_zfmisc_1, conjecture,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.48/0.68       ( k2_tarski @ A @ B ) ))).
% 0.48/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.68    (~( ![A:$i,B:$i]:
% 0.48/0.68        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.48/0.68          ( k2_tarski @ A @ B ) ) )),
% 0.48/0.68    inference('cnf.neg', [status(esa)], [t14_zfmisc_1])).
% 0.48/0.68  thf('0', plain,
% 0.48/0.68      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_B))
% 0.48/0.68         != (k2_tarski @ sk_A @ sk_B))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf(t12_zfmisc_1, axiom,
% 0.48/0.68    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.48/0.68  thf('1', plain,
% 0.48/0.68      (![X48 : $i, X49 : $i]:
% 0.48/0.68         (r1_tarski @ (k1_tarski @ X48) @ (k2_tarski @ X48 @ X49))),
% 0.48/0.68      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.48/0.68  thf(t28_xboole_1, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.48/0.68  thf('2', plain,
% 0.48/0.68      (![X7 : $i, X8 : $i]:
% 0.48/0.68         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.48/0.68      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.48/0.68  thf('3', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k3_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.48/0.68           = (k1_tarski @ X1))),
% 0.48/0.68      inference('sup-', [status(thm)], ['1', '2'])).
% 0.48/0.68  thf(commutativity_k3_xboole_0, axiom,
% 0.48/0.68    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.48/0.68  thf('4', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.48/0.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.48/0.68  thf(t100_xboole_1, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.48/0.68  thf('5', plain,
% 0.48/0.68      (![X5 : $i, X6 : $i]:
% 0.48/0.68         ((k4_xboole_0 @ X5 @ X6)
% 0.48/0.68           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.48/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.48/0.68  thf('6', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k4_xboole_0 @ X0 @ X1)
% 0.48/0.68           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.48/0.68      inference('sup+', [status(thm)], ['4', '5'])).
% 0.48/0.68  thf(idempotence_k3_xboole_0, axiom,
% 0.48/0.68    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.48/0.68  thf('7', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 0.48/0.68      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.48/0.68  thf('8', plain,
% 0.48/0.68      (![X5 : $i, X6 : $i]:
% 0.48/0.68         ((k4_xboole_0 @ X5 @ X6)
% 0.48/0.68           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.48/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.48/0.68  thf('9', plain,
% 0.48/0.68      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.48/0.68      inference('sup+', [status(thm)], ['7', '8'])).
% 0.48/0.68  thf(t91_xboole_1, axiom,
% 0.48/0.68    (![A:$i,B:$i,C:$i]:
% 0.48/0.68     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.48/0.68       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.48/0.68  thf('10', plain,
% 0.48/0.68      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.48/0.68         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 0.48/0.68           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 0.48/0.68      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.48/0.68  thf(commutativity_k5_xboole_0, axiom,
% 0.48/0.68    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.48/0.68  thf('11', plain,
% 0.48/0.68      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.48/0.68      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.48/0.68  thf('12', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.68         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.48/0.68           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.48/0.68      inference('sup+', [status(thm)], ['10', '11'])).
% 0.48/0.68  thf('13', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 0.48/0.68           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.48/0.68      inference('sup+', [status(thm)], ['9', '12'])).
% 0.48/0.68  thf(t40_xboole_1, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.48/0.68  thf('14', plain,
% 0.48/0.68      (![X10 : $i, X11 : $i]:
% 0.48/0.68         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 0.48/0.68           = (k4_xboole_0 @ X10 @ X11))),
% 0.48/0.68      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.48/0.68  thf(t3_boole, axiom,
% 0.48/0.68    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.48/0.68  thf('15', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.48/0.68      inference('cnf', [status(esa)], [t3_boole])).
% 0.48/0.68  thf('16', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.48/0.68      inference('sup+', [status(thm)], ['14', '15'])).
% 0.48/0.68  thf(t98_xboole_1, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.48/0.68  thf('17', plain,
% 0.48/0.68      (![X18 : $i, X19 : $i]:
% 0.48/0.68         ((k2_xboole_0 @ X18 @ X19)
% 0.48/0.68           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 0.48/0.68      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.48/0.68  thf('18', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.48/0.68           = (k5_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.48/0.68      inference('sup+', [status(thm)], ['16', '17'])).
% 0.48/0.68  thf('19', plain,
% 0.48/0.68      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.48/0.68      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.48/0.68  thf(t5_boole, axiom,
% 0.48/0.68    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.48/0.68  thf('20', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.48/0.68      inference('cnf', [status(esa)], [t5_boole])).
% 0.48/0.68  thf('21', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.48/0.68      inference('sup+', [status(thm)], ['19', '20'])).
% 0.48/0.68  thf('22', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.48/0.68      inference('demod', [status(thm)], ['18', '21'])).
% 0.48/0.68  thf('23', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.48/0.68      inference('sup+', [status(thm)], ['14', '15'])).
% 0.48/0.68  thf('24', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.48/0.68      inference('cnf', [status(esa)], [t3_boole])).
% 0.48/0.68  thf('25', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.48/0.68      inference('sup+', [status(thm)], ['23', '24'])).
% 0.48/0.68  thf('26', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.48/0.68      inference('demod', [status(thm)], ['22', '25'])).
% 0.48/0.68  thf('27', plain,
% 0.48/0.68      (![X10 : $i, X11 : $i]:
% 0.48/0.68         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 0.48/0.68           = (k4_xboole_0 @ X10 @ X11))),
% 0.48/0.68      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.48/0.68  thf('28', plain,
% 0.48/0.68      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.48/0.68      inference('sup+', [status(thm)], ['26', '27'])).
% 0.48/0.68  thf('29', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.48/0.68      inference('demod', [status(thm)], ['22', '25'])).
% 0.48/0.68  thf(t7_xboole_1, axiom,
% 0.48/0.68    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.48/0.68  thf('30', plain,
% 0.48/0.68      (![X13 : $i, X14 : $i]: (r1_tarski @ X13 @ (k2_xboole_0 @ X13 @ X14))),
% 0.48/0.68      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.48/0.68  thf('31', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.48/0.68      inference('sup+', [status(thm)], ['29', '30'])).
% 0.48/0.68  thf('32', plain,
% 0.48/0.68      (![X7 : $i, X8 : $i]:
% 0.48/0.68         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.48/0.68      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.48/0.68  thf('33', plain,
% 0.48/0.68      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.48/0.68      inference('sup-', [status(thm)], ['31', '32'])).
% 0.48/0.68  thf('34', plain,
% 0.48/0.68      (![X5 : $i, X6 : $i]:
% 0.48/0.68         ((k4_xboole_0 @ X5 @ X6)
% 0.48/0.68           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.48/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.48/0.68  thf('35', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.48/0.68           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.48/0.68      inference('sup+', [status(thm)], ['33', '34'])).
% 0.48/0.68  thf('36', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.48/0.68      inference('sup+', [status(thm)], ['19', '20'])).
% 0.48/0.68  thf('37', plain,
% 0.48/0.68      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.48/0.68      inference('demod', [status(thm)], ['35', '36'])).
% 0.48/0.68  thf('38', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.48/0.68      inference('demod', [status(thm)], ['28', '37'])).
% 0.48/0.68  thf('39', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.48/0.68      inference('cnf', [status(esa)], [t5_boole])).
% 0.48/0.68  thf('40', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 0.48/0.68      inference('sup+', [status(thm)], ['38', '39'])).
% 0.48/0.68  thf('41', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 0.48/0.68      inference('demod', [status(thm)], ['13', '40'])).
% 0.48/0.68  thf('42', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 0.48/0.68           = (X1))),
% 0.48/0.68      inference('sup+', [status(thm)], ['6', '41'])).
% 0.48/0.68  thf('43', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k5_xboole_0 @ (k1_tarski @ X0) @ 
% 0.48/0.68           (k4_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k1_tarski @ X0)))
% 0.48/0.68           = (k2_tarski @ X0 @ X1))),
% 0.48/0.68      inference('sup+', [status(thm)], ['3', '42'])).
% 0.48/0.68  thf('44', plain,
% 0.48/0.68      (![X18 : $i, X19 : $i]:
% 0.48/0.68         ((k2_xboole_0 @ X18 @ X19)
% 0.48/0.68           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 0.48/0.68      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.48/0.68  thf('45', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))
% 0.48/0.68           = (k2_tarski @ X0 @ X1))),
% 0.48/0.68      inference('demod', [status(thm)], ['43', '44'])).
% 0.48/0.68  thf('46', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.48/0.68      inference('demod', [status(thm)], ['0', '45'])).
% 0.48/0.68  thf('47', plain, ($false), inference('simplify', [status(thm)], ['46'])).
% 0.48/0.68  
% 0.48/0.68  % SZS output end Refutation
% 0.48/0.68  
% 0.48/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
