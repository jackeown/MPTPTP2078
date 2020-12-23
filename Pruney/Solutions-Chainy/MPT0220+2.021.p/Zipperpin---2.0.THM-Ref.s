%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.je1SnxeUoc

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:21 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   71 (  93 expanded)
%              Number of leaves         :   23 (  37 expanded)
%              Depth                    :   14
%              Number of atoms          :  458 ( 608 expanded)
%              Number of equality atoms :   55 (  77 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X50: $i,X51: $i] :
      ( r1_tarski @ ( k1_tarski @ X50 ) @ ( k2_tarski @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k5_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('11',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('22',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('25',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('27',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
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
    inference('sup+',[status(thm)],['24','25'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('30',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('31',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
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
    inference('sup+',[status(thm)],['21','22'])).

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
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['19','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k4_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['9','41'])).

thf('43',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','44'])).

thf('46',plain,(
    $false ),
    inference(simplify,[status(thm)],['45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.je1SnxeUoc
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:23:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.52/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.52/0.73  % Solved by: fo/fo7.sh
% 0.52/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.73  % done 678 iterations in 0.312s
% 0.52/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.52/0.73  % SZS output start Refutation
% 0.52/0.73  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.52/0.73  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.52/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.73  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.52/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.52/0.73  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.52/0.73  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.52/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.73  thf(t14_zfmisc_1, conjecture,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.52/0.73       ( k2_tarski @ A @ B ) ))).
% 0.52/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.73    (~( ![A:$i,B:$i]:
% 0.52/0.73        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.52/0.73          ( k2_tarski @ A @ B ) ) )),
% 0.52/0.73    inference('cnf.neg', [status(esa)], [t14_zfmisc_1])).
% 0.52/0.73  thf('0', plain,
% 0.52/0.73      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_B))
% 0.52/0.73         != (k2_tarski @ sk_A @ sk_B))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf(t12_zfmisc_1, axiom,
% 0.52/0.73    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.52/0.73  thf('1', plain,
% 0.52/0.73      (![X50 : $i, X51 : $i]:
% 0.52/0.73         (r1_tarski @ (k1_tarski @ X50) @ (k2_tarski @ X50 @ X51))),
% 0.52/0.73      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.52/0.73  thf(t28_xboole_1, axiom,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.52/0.73  thf('2', plain,
% 0.52/0.73      (![X9 : $i, X10 : $i]:
% 0.52/0.73         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.52/0.73      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.52/0.73  thf('3', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         ((k3_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.52/0.73           = (k1_tarski @ X1))),
% 0.52/0.73      inference('sup-', [status(thm)], ['1', '2'])).
% 0.52/0.73  thf(commutativity_k3_xboole_0, axiom,
% 0.52/0.73    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.52/0.73  thf('4', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.52/0.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.52/0.73  thf(t100_xboole_1, axiom,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.52/0.73  thf('5', plain,
% 0.52/0.73      (![X7 : $i, X8 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ X7 @ X8)
% 0.52/0.73           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.52/0.73      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.52/0.73  thf('6', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ X0 @ X1)
% 0.52/0.73           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.52/0.73      inference('sup+', [status(thm)], ['4', '5'])).
% 0.52/0.73  thf('7', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k1_tarski @ X0))
% 0.52/0.73           = (k5_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k1_tarski @ X0)))),
% 0.52/0.73      inference('sup+', [status(thm)], ['3', '6'])).
% 0.52/0.73  thf(commutativity_k5_xboole_0, axiom,
% 0.52/0.73    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.52/0.73  thf('8', plain,
% 0.52/0.73      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.52/0.73      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.52/0.73  thf('9', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k1_tarski @ X0))
% 0.52/0.73           = (k5_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1)))),
% 0.52/0.73      inference('demod', [status(thm)], ['7', '8'])).
% 0.52/0.73  thf(d10_xboole_0, axiom,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.52/0.73  thf('10', plain,
% 0.52/0.73      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.52/0.73      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.52/0.73  thf('11', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.52/0.73      inference('simplify', [status(thm)], ['10'])).
% 0.52/0.73  thf('12', plain,
% 0.52/0.73      (![X9 : $i, X10 : $i]:
% 0.52/0.73         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.52/0.73      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.52/0.73  thf('13', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.52/0.73      inference('sup-', [status(thm)], ['11', '12'])).
% 0.52/0.73  thf('14', plain,
% 0.52/0.73      (![X7 : $i, X8 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ X7 @ X8)
% 0.52/0.73           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.52/0.73      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.52/0.73  thf('15', plain,
% 0.52/0.73      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['13', '14'])).
% 0.52/0.73  thf(t91_xboole_1, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i]:
% 0.52/0.73     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.52/0.73       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.52/0.73  thf('16', plain,
% 0.52/0.73      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.52/0.73         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.52/0.73           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 0.52/0.73      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.52/0.73  thf('17', plain,
% 0.52/0.73      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.52/0.73      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.52/0.73  thf('18', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.73         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.52/0.73           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.52/0.73      inference('sup+', [status(thm)], ['16', '17'])).
% 0.52/0.73  thf('19', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.52/0.73           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.52/0.73      inference('sup+', [status(thm)], ['15', '18'])).
% 0.52/0.73  thf(t98_xboole_1, axiom,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.52/0.73  thf('20', plain,
% 0.52/0.73      (![X20 : $i, X21 : $i]:
% 0.52/0.73         ((k2_xboole_0 @ X20 @ X21)
% 0.52/0.73           = (k5_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20)))),
% 0.52/0.73      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.52/0.73  thf('21', plain,
% 0.52/0.73      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.52/0.73      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.52/0.73  thf(t5_boole, axiom,
% 0.52/0.73    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.52/0.73  thf('22', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.52/0.73      inference('cnf', [status(esa)], [t5_boole])).
% 0.52/0.73  thf('23', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['21', '22'])).
% 0.52/0.73  thf('24', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['20', '23'])).
% 0.52/0.73  thf(t3_boole, axiom,
% 0.52/0.73    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.52/0.73  thf('25', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.52/0.73      inference('cnf', [status(esa)], [t3_boole])).
% 0.52/0.73  thf('26', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['24', '25'])).
% 0.52/0.73  thf(t40_xboole_1, axiom,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.52/0.73  thf('27', plain,
% 0.52/0.73      (![X12 : $i, X13 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ X13)
% 0.52/0.73           = (k4_xboole_0 @ X12 @ X13))),
% 0.52/0.73      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.52/0.73  thf('28', plain,
% 0.52/0.73      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['26', '27'])).
% 0.52/0.73  thf('29', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['24', '25'])).
% 0.52/0.73  thf(t7_xboole_1, axiom,
% 0.52/0.73    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.52/0.73  thf('30', plain,
% 0.52/0.73      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 0.52/0.73      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.52/0.73  thf('31', plain,
% 0.52/0.73      (![X9 : $i, X10 : $i]:
% 0.52/0.73         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.52/0.73      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.52/0.73  thf('32', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.52/0.73      inference('sup-', [status(thm)], ['30', '31'])).
% 0.52/0.73  thf('33', plain,
% 0.52/0.73      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['29', '32'])).
% 0.52/0.73  thf('34', plain,
% 0.52/0.73      (![X7 : $i, X8 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ X7 @ X8)
% 0.52/0.73           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.52/0.73      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.52/0.73  thf('35', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.52/0.73           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['33', '34'])).
% 0.52/0.73  thf('36', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['21', '22'])).
% 0.52/0.73  thf('37', plain,
% 0.52/0.73      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.52/0.73      inference('demod', [status(thm)], ['35', '36'])).
% 0.52/0.73  thf('38', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.52/0.73      inference('demod', [status(thm)], ['28', '37'])).
% 0.52/0.73  thf('39', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.52/0.73      inference('cnf', [status(esa)], [t5_boole])).
% 0.52/0.73  thf('40', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 0.52/0.73      inference('sup+', [status(thm)], ['38', '39'])).
% 0.52/0.73  thf('41', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.52/0.73      inference('demod', [status(thm)], ['19', '40'])).
% 0.52/0.73  thf('42', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         ((k2_tarski @ X0 @ X1)
% 0.52/0.73           = (k5_xboole_0 @ (k1_tarski @ X0) @ 
% 0.52/0.73              (k4_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k1_tarski @ X0))))),
% 0.52/0.73      inference('sup+', [status(thm)], ['9', '41'])).
% 0.52/0.73  thf('43', plain,
% 0.52/0.73      (![X20 : $i, X21 : $i]:
% 0.52/0.73         ((k2_xboole_0 @ X20 @ X21)
% 0.52/0.73           = (k5_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20)))),
% 0.52/0.73      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.52/0.73  thf('44', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         ((k2_tarski @ X0 @ X1)
% 0.52/0.73           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1)))),
% 0.52/0.73      inference('demod', [status(thm)], ['42', '43'])).
% 0.52/0.73  thf('45', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.52/0.73      inference('demod', [status(thm)], ['0', '44'])).
% 0.52/0.73  thf('46', plain, ($false), inference('simplify', [status(thm)], ['45'])).
% 0.52/0.73  
% 0.52/0.73  % SZS output end Refutation
% 0.52/0.73  
% 0.52/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
