%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GlbB1uA6Hs

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:58 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 152 expanded)
%              Number of leaves         :   19 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :  597 (1604 expanded)
%              Number of equality atoms :   51 ( 141 expanded)
%              Maximal formula depth    :   16 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(t98_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ A @ C @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k1_enumset1 @ A @ B @ C )
        = ( k1_enumset1 @ A @ C @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t98_enumset1])).

thf('0',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t78_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_enumset1 @ A @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('1',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k3_enumset1 @ X28 @ X28 @ X28 @ X29 @ X30 )
      = ( k1_enumset1 @ X28 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t78_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k3_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26 )
      = ( k2_enumset1 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('3',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k2_enumset1 @ X28 @ X28 @ X29 @ X30 )
      = ( k1_enumset1 @ X28 @ X29 @ X30 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X21 @ X21 @ X22 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t47_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_enumset1 @ X3 @ X4 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_enumset1 @ X3 @ X4 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X0 @ X0 @ X0 @ X1 )
      = ( k3_enumset1 @ X2 @ X1 @ X1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('15',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_enumset1 @ X3 @ X4 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t76_enumset1,axiom,(
    ! [A: $i] :
      ( ( k1_enumset1 @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('18',plain,(
    ! [X27: $i] :
      ( ( k1_enumset1 @ X27 @ X27 @ X27 )
      = ( k1_tarski @ X27 ) ) ),
    inference(cnf,[status(esa)],[t76_enumset1])).

thf('19',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X21 @ X21 @ X22 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('20',plain,(
    ! [X27: $i] :
      ( ( k2_tarski @ X27 @ X27 )
      = ( k1_tarski @ X27 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k3_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26 )
      = ( k2_enumset1 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t57_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k3_enumset1 @ C @ D @ E @ F @ G ) ) ) )).

thf('23',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k5_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k2_tarski @ X7 @ X8 ) @ ( k3_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t57_enumset1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X5 @ X4 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k3_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26 )
      = ( k2_enumset1 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t60_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ) )).

thf('26',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k5_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 ) @ ( k2_tarski @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t60_enumset1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X5 @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X4 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X27: $i] :
      ( ( k2_tarski @ X27 @ X27 )
      = ( k1_tarski @ X27 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('30',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_enumset1 @ X3 @ X4 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['21','31'])).

thf('33',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k3_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26 )
      = ( k2_enumset1 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k2_enumset1 @ X28 @ X28 @ X29 @ X30 )
      = ( k1_enumset1 @ X28 @ X29 @ X30 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X1 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X1 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','36'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X0 @ X1 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','37','38'])).

thf('40',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','39'])).

thf('41',plain,(
    $false ),
    inference(simplify,[status(thm)],['40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GlbB1uA6Hs
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:37:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.43/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.62  % Solved by: fo/fo7.sh
% 0.43/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.62  % done 359 iterations in 0.192s
% 0.43/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.62  % SZS output start Refutation
% 0.43/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.43/0.62  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.43/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.43/0.62  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.43/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.43/0.62  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.43/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.43/0.62  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.43/0.62  thf(t98_enumset1, conjecture,
% 0.43/0.62    (![A:$i,B:$i,C:$i]:
% 0.43/0.62     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ A @ C @ B ) ))).
% 0.43/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.62    (~( ![A:$i,B:$i,C:$i]:
% 0.43/0.62        ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ A @ C @ B ) ) )),
% 0.43/0.62    inference('cnf.neg', [status(esa)], [t98_enumset1])).
% 0.43/0.62  thf('0', plain,
% 0.43/0.62      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.43/0.62         != (k1_enumset1 @ sk_A @ sk_C @ sk_B))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(t78_enumset1, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i]:
% 0.43/0.62     ( ( k3_enumset1 @ A @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.43/0.62  thf('1', plain,
% 0.43/0.62      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.43/0.62         ((k3_enumset1 @ X28 @ X28 @ X28 @ X29 @ X30)
% 0.43/0.62           = (k1_enumset1 @ X28 @ X29 @ X30))),
% 0.43/0.62      inference('cnf', [status(esa)], [t78_enumset1])).
% 0.43/0.62  thf(t72_enumset1, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.62     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.43/0.62  thf('2', plain,
% 0.43/0.62      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.43/0.62         ((k3_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26)
% 0.43/0.62           = (k2_enumset1 @ X23 @ X24 @ X25 @ X26))),
% 0.43/0.62      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.43/0.62  thf('3', plain,
% 0.43/0.62      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.43/0.62         ((k2_enumset1 @ X28 @ X28 @ X29 @ X30)
% 0.43/0.62           = (k1_enumset1 @ X28 @ X29 @ X30))),
% 0.43/0.62      inference('demod', [status(thm)], ['1', '2'])).
% 0.43/0.62  thf(t70_enumset1, axiom,
% 0.43/0.62    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.43/0.62  thf('4', plain,
% 0.43/0.62      (![X21 : $i, X22 : $i]:
% 0.43/0.62         ((k1_enumset1 @ X21 @ X21 @ X22) = (k2_tarski @ X21 @ X22))),
% 0.43/0.62      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.43/0.62  thf('5', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['3', '4'])).
% 0.43/0.62  thf(commutativity_k2_tarski, axiom,
% 0.43/0.62    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.43/0.62  thf('6', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.43/0.62      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.43/0.62  thf('7', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((k2_tarski @ X0 @ X1) = (k2_enumset1 @ X1 @ X1 @ X1 @ X0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['5', '6'])).
% 0.43/0.62  thf('8', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['3', '4'])).
% 0.43/0.62  thf('9', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1) = (k2_enumset1 @ X1 @ X1 @ X1 @ X0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['7', '8'])).
% 0.43/0.62  thf(t47_enumset1, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.43/0.62     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.43/0.62       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ))).
% 0.43/0.62  thf('10', plain,
% 0.43/0.62      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.43/0.62         ((k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6)
% 0.43/0.62           = (k2_xboole_0 @ (k1_tarski @ X2) @ 
% 0.43/0.62              (k2_enumset1 @ X3 @ X4 @ X5 @ X6)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.43/0.62  thf('11', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.62         ((k3_enumset1 @ X2 @ X0 @ X0 @ X0 @ X1)
% 0.43/0.62           = (k2_xboole_0 @ (k1_tarski @ X2) @ 
% 0.43/0.62              (k2_enumset1 @ X1 @ X1 @ X1 @ X0)))),
% 0.43/0.62      inference('sup+', [status(thm)], ['9', '10'])).
% 0.43/0.62  thf('12', plain,
% 0.43/0.62      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.43/0.62         ((k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6)
% 0.43/0.62           = (k2_xboole_0 @ (k1_tarski @ X2) @ 
% 0.43/0.62              (k2_enumset1 @ X3 @ X4 @ X5 @ X6)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.43/0.62  thf('13', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.62         ((k3_enumset1 @ X2 @ X0 @ X0 @ X0 @ X1)
% 0.43/0.62           = (k3_enumset1 @ X2 @ X1 @ X1 @ X1 @ X0))),
% 0.43/0.62      inference('demod', [status(thm)], ['11', '12'])).
% 0.43/0.62  thf('14', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['3', '4'])).
% 0.43/0.62  thf('15', plain,
% 0.43/0.62      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.43/0.62         ((k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6)
% 0.43/0.62           = (k2_xboole_0 @ (k1_tarski @ X2) @ 
% 0.43/0.62              (k2_enumset1 @ X3 @ X4 @ X5 @ X6)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.43/0.62  thf('16', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.62         ((k3_enumset1 @ X2 @ X1 @ X1 @ X1 @ X0)
% 0.43/0.62           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.43/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.43/0.62  thf('17', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['3', '4'])).
% 0.43/0.62  thf(t76_enumset1, axiom,
% 0.43/0.62    (![A:$i]: ( ( k1_enumset1 @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.43/0.62  thf('18', plain,
% 0.43/0.62      (![X27 : $i]: ((k1_enumset1 @ X27 @ X27 @ X27) = (k1_tarski @ X27))),
% 0.43/0.62      inference('cnf', [status(esa)], [t76_enumset1])).
% 0.43/0.62  thf('19', plain,
% 0.43/0.62      (![X21 : $i, X22 : $i]:
% 0.43/0.62         ((k1_enumset1 @ X21 @ X21 @ X22) = (k2_tarski @ X21 @ X22))),
% 0.43/0.62      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.43/0.62  thf('20', plain,
% 0.43/0.62      (![X27 : $i]: ((k2_tarski @ X27 @ X27) = (k1_tarski @ X27))),
% 0.43/0.62      inference('demod', [status(thm)], ['18', '19'])).
% 0.43/0.62  thf('21', plain,
% 0.43/0.62      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['17', '20'])).
% 0.43/0.62  thf('22', plain,
% 0.43/0.62      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.43/0.62         ((k3_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26)
% 0.43/0.62           = (k2_enumset1 @ X23 @ X24 @ X25 @ X26))),
% 0.43/0.62      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.43/0.62  thf(t57_enumset1, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.43/0.62     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.43/0.62       ( k2_xboole_0 @
% 0.43/0.62         ( k2_tarski @ A @ B ) @ ( k3_enumset1 @ C @ D @ E @ F @ G ) ) ))).
% 0.43/0.62  thf('23', plain,
% 0.43/0.62      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.43/0.62         ((k5_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13)
% 0.43/0.62           = (k2_xboole_0 @ (k2_tarski @ X7 @ X8) @ 
% 0.43/0.62              (k3_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t57_enumset1])).
% 0.43/0.62  thf('24', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.43/0.62         ((k5_enumset1 @ X5 @ X4 @ X3 @ X3 @ X2 @ X1 @ X0)
% 0.43/0.62           = (k2_xboole_0 @ (k2_tarski @ X5 @ X4) @ 
% 0.43/0.62              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 0.43/0.62      inference('sup+', [status(thm)], ['22', '23'])).
% 0.43/0.62  thf('25', plain,
% 0.43/0.62      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.43/0.62         ((k3_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26)
% 0.43/0.62           = (k2_enumset1 @ X23 @ X24 @ X25 @ X26))),
% 0.43/0.62      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.43/0.62  thf(t60_enumset1, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.43/0.62     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.43/0.62       ( k2_xboole_0 @
% 0.43/0.62         ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ))).
% 0.43/0.62  thf('26', plain,
% 0.43/0.62      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.43/0.62         ((k5_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20)
% 0.43/0.62           = (k2_xboole_0 @ (k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18) @ 
% 0.43/0.62              (k2_tarski @ X19 @ X20)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t60_enumset1])).
% 0.43/0.62  thf('27', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.43/0.62         ((k5_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4)
% 0.43/0.62           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.43/0.62              (k2_tarski @ X5 @ X4)))),
% 0.43/0.62      inference('sup+', [status(thm)], ['25', '26'])).
% 0.43/0.62  thf('28', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.43/0.62         ((k2_xboole_0 @ (k2_tarski @ X4 @ X4) @ 
% 0.43/0.62           (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.43/0.62           = (k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X3 @ X2) @ 
% 0.43/0.62              (k2_tarski @ X1 @ X0)))),
% 0.43/0.62      inference('sup+', [status(thm)], ['24', '27'])).
% 0.43/0.62  thf('29', plain,
% 0.43/0.62      (![X27 : $i]: ((k2_tarski @ X27 @ X27) = (k1_tarski @ X27))),
% 0.43/0.62      inference('demod', [status(thm)], ['18', '19'])).
% 0.43/0.62  thf('30', plain,
% 0.43/0.62      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.43/0.62         ((k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6)
% 0.43/0.62           = (k2_xboole_0 @ (k1_tarski @ X2) @ 
% 0.43/0.62              (k2_enumset1 @ X3 @ X4 @ X5 @ X6)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.43/0.62  thf('31', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.43/0.62         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.43/0.62           = (k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X3 @ X2) @ 
% 0.43/0.62              (k2_tarski @ X1 @ X0)))),
% 0.43/0.62      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.43/0.62  thf('32', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.62         ((k3_enumset1 @ X0 @ X0 @ X0 @ X2 @ X1)
% 0.43/0.62           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 0.43/0.62      inference('sup+', [status(thm)], ['21', '31'])).
% 0.43/0.62  thf('33', plain,
% 0.43/0.62      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.43/0.62         ((k3_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26)
% 0.43/0.62           = (k2_enumset1 @ X23 @ X24 @ X25 @ X26))),
% 0.43/0.62      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.43/0.62  thf('34', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.62         ((k2_enumset1 @ X0 @ X0 @ X2 @ X1)
% 0.43/0.62           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 0.43/0.62      inference('demod', [status(thm)], ['32', '33'])).
% 0.43/0.62  thf('35', plain,
% 0.43/0.62      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.43/0.62         ((k2_enumset1 @ X28 @ X28 @ X29 @ X30)
% 0.43/0.62           = (k1_enumset1 @ X28 @ X29 @ X30))),
% 0.43/0.62      inference('demod', [status(thm)], ['1', '2'])).
% 0.43/0.62  thf('36', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.62         ((k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0))
% 0.43/0.62           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['34', '35'])).
% 0.43/0.62  thf('37', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.62         ((k3_enumset1 @ X2 @ X1 @ X1 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.43/0.62      inference('demod', [status(thm)], ['16', '36'])).
% 0.43/0.62  thf('38', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.62         ((k3_enumset1 @ X2 @ X1 @ X1 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.43/0.62      inference('demod', [status(thm)], ['16', '36'])).
% 0.43/0.62  thf('39', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.62         ((k1_enumset1 @ X2 @ X0 @ X1) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.43/0.62      inference('demod', [status(thm)], ['13', '37', '38'])).
% 0.43/0.62  thf('40', plain,
% 0.43/0.62      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.43/0.62         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.43/0.62      inference('demod', [status(thm)], ['0', '39'])).
% 0.43/0.62  thf('41', plain, ($false), inference('simplify', [status(thm)], ['40'])).
% 0.43/0.62  
% 0.43/0.62  % SZS output end Refutation
% 0.43/0.62  
% 0.45/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
