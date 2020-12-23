%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.49HL6BNtSz

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:32 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   62 (  97 expanded)
%              Number of leaves         :   20 (  41 expanded)
%              Depth                    :   12
%              Number of atoms          :  618 ( 944 expanded)
%              Number of equality atoms :   50 (  85 expanded)
%              Maximal formula depth    :   18 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t72_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k3_enumset1 @ A @ A @ B @ C @ D )
        = ( k2_enumset1 @ A @ B @ C @ D ) ) ),
    inference('cnf.neg',[status(esa)],[t72_enumset1])).

thf('0',plain,(
    ( k3_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X47: $i] :
      ( ( k2_tarski @ X47 @ X47 )
      = ( k1_tarski @ X47 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('2',plain,(
    ! [X47: $i] :
      ( ( k2_tarski @ X47 @ X47 )
      = ( k1_tarski @ X47 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_tarski @ X14 @ X15 )
      = ( k2_xboole_0 @ ( k1_tarski @ X14 ) @ ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X3 ) @ ( k2_tarski @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('7',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( k2_enumset1 @ X50 @ X50 @ X51 @ X52 )
      = ( k1_enumset1 @ X50 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( k2_enumset1 @ X50 @ X50 @ X51 @ X52 )
      = ( k1_enumset1 @ X50 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(l75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k6_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) @ ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l75_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X2 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_enumset1 @ X6 @ X5 @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X1 @ X1 @ X0 @ X0 @ X5 @ X4 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( k2_enumset1 @ X50 @ X50 @ X51 @ X52 )
      = ( k1_enumset1 @ X50 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t47_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ) )).

thf('14',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( k3_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 )
      = ( k2_xboole_0 @ ( k1_tarski @ X20 ) @ ( k2_enumset1 @ X21 @ X22 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('16',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k2_enumset1 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k1_tarski @ X16 ) @ ( k1_enumset1 @ X17 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('19',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k2_enumset1 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k1_tarski @ X16 ) @ ( k1_enumset1 @ X17 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X47: $i] :
      ( ( k2_tarski @ X47 @ X47 )
      = ( k1_tarski @ X47 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('22',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X3 ) @ ( k2_tarski @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( k2_enumset1 @ X50 @ X50 @ X51 @ X52 )
      = ( k1_enumset1 @ X50 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X1 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','26'])).

thf(t66_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_enumset1 @ F @ G @ H ) ) ) )).

thf('28',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( k6_enumset1 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X39 @ X40 @ X41 @ X42 @ X43 ) @ ( k1_enumset1 @ X44 @ X45 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[t66_enumset1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X2 @ X1 @ X1 @ X0 @ X0 @ X5 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_enumset1 @ X5 @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X3 @ X3 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X3 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','29'])).

thf('31',plain,(
    ! [X47: $i] :
      ( ( k2_tarski @ X47 @ X47 )
      = ( k1_tarski @ X47 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('32',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( k3_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 )
      = ( k2_xboole_0 @ ( k1_tarski @ X20 ) @ ( k2_enumset1 @ X21 @ X22 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X0 @ X4 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('35',plain,(
    ! [X47: $i] :
      ( ( k2_tarski @ X47 @ X47 )
      = ( k1_tarski @ X47 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('36',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k2_enumset1 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k1_tarski @ X16 ) @ ( k1_enumset1 @ X17 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_enumset1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','33','34','37'])).

thf('39',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','38'])).

thf('40',plain,(
    $false ),
    inference(simplify,[status(thm)],['39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.49HL6BNtSz
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.19/0.33  % DateTime   : Tue Dec  1 14:11:00 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.59/0.80  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.80  % Solved by: fo/fo7.sh
% 0.59/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.80  % done 525 iterations in 0.361s
% 0.59/0.80  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.80  % SZS output start Refutation
% 0.59/0.80  thf(sk_C_type, type, sk_C: $i).
% 0.59/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.80  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.80  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.59/0.80                                           $i > $i).
% 0.59/0.80  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.59/0.80  thf(sk_D_type, type, sk_D: $i).
% 0.59/0.80  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.59/0.80  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.59/0.80  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.59/0.80  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.59/0.80  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.59/0.80  thf(t72_enumset1, conjecture,
% 0.59/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.80     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.59/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.80    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.80        ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ) )),
% 0.59/0.80    inference('cnf.neg', [status(esa)], [t72_enumset1])).
% 0.59/0.80  thf('0', plain,
% 0.59/0.80      (((k3_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.59/0.80         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf(t69_enumset1, axiom,
% 0.59/0.80    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.59/0.80  thf('1', plain, (![X47 : $i]: ((k2_tarski @ X47 @ X47) = (k1_tarski @ X47))),
% 0.59/0.80      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.59/0.80  thf('2', plain, (![X47 : $i]: ((k2_tarski @ X47 @ X47) = (k1_tarski @ X47))),
% 0.59/0.80      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.59/0.80  thf(t41_enumset1, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( k2_tarski @ A @ B ) =
% 0.59/0.80       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.59/0.80  thf('3', plain,
% 0.59/0.80      (![X14 : $i, X15 : $i]:
% 0.59/0.80         ((k2_tarski @ X14 @ X15)
% 0.59/0.80           = (k2_xboole_0 @ (k1_tarski @ X14) @ (k1_tarski @ X15)))),
% 0.59/0.80      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.59/0.80  thf('4', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((k2_tarski @ X0 @ X1)
% 0.59/0.80           = (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X1)))),
% 0.59/0.80      inference('sup+', [status(thm)], ['2', '3'])).
% 0.59/0.80  thf('5', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((k2_tarski @ X1 @ X0)
% 0.59/0.80           = (k2_xboole_0 @ (k2_tarski @ X1 @ X1) @ (k2_tarski @ X0 @ X0)))),
% 0.59/0.80      inference('sup+', [status(thm)], ['1', '4'])).
% 0.59/0.80  thf(l53_enumset1, axiom,
% 0.59/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.80     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.59/0.80       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.59/0.80  thf('6', plain,
% 0.59/0.80      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.59/0.80         ((k2_enumset1 @ X2 @ X3 @ X4 @ X5)
% 0.59/0.80           = (k2_xboole_0 @ (k2_tarski @ X2 @ X3) @ (k2_tarski @ X4 @ X5)))),
% 0.59/0.80      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.59/0.80  thf(t71_enumset1, axiom,
% 0.59/0.80    (![A:$i,B:$i,C:$i]:
% 0.59/0.80     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.59/0.80  thf('7', plain,
% 0.59/0.80      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.59/0.80         ((k2_enumset1 @ X50 @ X50 @ X51 @ X52)
% 0.59/0.80           = (k1_enumset1 @ X50 @ X51 @ X52))),
% 0.59/0.80      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.59/0.80  thf('8', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X0))),
% 0.59/0.80      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.59/0.80  thf('9', plain,
% 0.59/0.80      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.59/0.80         ((k2_enumset1 @ X50 @ X50 @ X51 @ X52)
% 0.59/0.80           = (k1_enumset1 @ X50 @ X51 @ X52))),
% 0.59/0.80      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.59/0.80  thf(l75_enumset1, axiom,
% 0.59/0.80    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.59/0.80     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.59/0.80       ( k2_xboole_0 @
% 0.59/0.80         ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ))).
% 0.59/0.80  thf('10', plain,
% 0.59/0.80      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, 
% 0.59/0.80         X13 : $i]:
% 0.59/0.80         ((k6_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13)
% 0.59/0.80           = (k2_xboole_0 @ (k2_enumset1 @ X6 @ X7 @ X8 @ X9) @ 
% 0.59/0.80              (k2_enumset1 @ X10 @ X11 @ X12 @ X13)))),
% 0.59/0.80      inference('cnf', [status(esa)], [l75_enumset1])).
% 0.59/0.80  thf('11', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.59/0.80         ((k6_enumset1 @ X2 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3)
% 0.59/0.80           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 0.59/0.80              (k2_enumset1 @ X6 @ X5 @ X4 @ X3)))),
% 0.59/0.80      inference('sup+', [status(thm)], ['9', '10'])).
% 0.59/0.80  thf('12', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.59/0.80         ((k6_enumset1 @ X1 @ X1 @ X0 @ X0 @ X5 @ X4 @ X3 @ X2)
% 0.59/0.80           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 0.59/0.80              (k2_enumset1 @ X5 @ X4 @ X3 @ X2)))),
% 0.59/0.80      inference('sup+', [status(thm)], ['8', '11'])).
% 0.59/0.80  thf('13', plain,
% 0.59/0.80      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.59/0.80         ((k2_enumset1 @ X50 @ X50 @ X51 @ X52)
% 0.59/0.80           = (k1_enumset1 @ X50 @ X51 @ X52))),
% 0.59/0.80      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.59/0.80  thf(t47_enumset1, axiom,
% 0.59/0.80    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.59/0.80     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.59/0.80       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ))).
% 0.59/0.80  thf('14', plain,
% 0.59/0.80      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.59/0.80         ((k3_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24)
% 0.59/0.80           = (k2_xboole_0 @ (k1_tarski @ X20) @ 
% 0.59/0.80              (k2_enumset1 @ X21 @ X22 @ X23 @ X24)))),
% 0.59/0.80      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.59/0.80  thf('15', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.80         ((k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0)
% 0.59/0.80           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.59/0.80      inference('sup+', [status(thm)], ['13', '14'])).
% 0.59/0.80  thf(t44_enumset1, axiom,
% 0.59/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.80     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.59/0.80       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.59/0.80  thf('16', plain,
% 0.59/0.80      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.59/0.80         ((k2_enumset1 @ X16 @ X17 @ X18 @ X19)
% 0.59/0.80           = (k2_xboole_0 @ (k1_tarski @ X16) @ (k1_enumset1 @ X17 @ X18 @ X19)))),
% 0.59/0.80      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.59/0.80  thf('17', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.80         ((k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0)
% 0.59/0.80           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.59/0.80      inference('demod', [status(thm)], ['15', '16'])).
% 0.59/0.80  thf('18', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X0))),
% 0.59/0.80      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.59/0.80  thf('19', plain,
% 0.59/0.80      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.59/0.80         ((k2_enumset1 @ X16 @ X17 @ X18 @ X19)
% 0.59/0.80           = (k2_xboole_0 @ (k1_tarski @ X16) @ (k1_enumset1 @ X17 @ X18 @ X19)))),
% 0.59/0.80      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.59/0.80  thf('20', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.80         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0)
% 0.59/0.80           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.59/0.80      inference('sup+', [status(thm)], ['18', '19'])).
% 0.59/0.80  thf('21', plain,
% 0.59/0.80      (![X47 : $i]: ((k2_tarski @ X47 @ X47) = (k1_tarski @ X47))),
% 0.59/0.80      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.59/0.80  thf('22', plain,
% 0.59/0.80      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.59/0.80         ((k2_enumset1 @ X2 @ X3 @ X4 @ X5)
% 0.59/0.80           = (k2_xboole_0 @ (k2_tarski @ X2 @ X3) @ (k2_tarski @ X4 @ X5)))),
% 0.59/0.80      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.59/0.80  thf('23', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.80         ((k2_enumset1 @ X0 @ X0 @ X2 @ X1)
% 0.59/0.80           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 0.59/0.80      inference('sup+', [status(thm)], ['21', '22'])).
% 0.59/0.80  thf('24', plain,
% 0.59/0.80      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.59/0.80         ((k2_enumset1 @ X50 @ X50 @ X51 @ X52)
% 0.59/0.80           = (k1_enumset1 @ X50 @ X51 @ X52))),
% 0.59/0.80      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.59/0.80  thf('25', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.80         ((k1_enumset1 @ X0 @ X2 @ X1)
% 0.59/0.80           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 0.59/0.80      inference('demod', [status(thm)], ['23', '24'])).
% 0.59/0.80  thf('26', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.80         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.59/0.80      inference('demod', [status(thm)], ['20', '25'])).
% 0.59/0.80  thf('27', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.80         ((k3_enumset1 @ X2 @ X1 @ X1 @ X0 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['17', '26'])).
% 0.59/0.80  thf(t66_enumset1, axiom,
% 0.59/0.80    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.59/0.80     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.59/0.80       ( k2_xboole_0 @
% 0.59/0.80         ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_enumset1 @ F @ G @ H ) ) ))).
% 0.59/0.80  thf('28', plain,
% 0.59/0.80      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, 
% 0.59/0.80         X46 : $i]:
% 0.59/0.80         ((k6_enumset1 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46)
% 0.59/0.80           = (k2_xboole_0 @ (k3_enumset1 @ X39 @ X40 @ X41 @ X42 @ X43) @ 
% 0.59/0.80              (k1_enumset1 @ X44 @ X45 @ X46)))),
% 0.59/0.80      inference('cnf', [status(esa)], [t66_enumset1])).
% 0.59/0.80  thf('29', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.59/0.80         ((k6_enumset1 @ X2 @ X1 @ X1 @ X0 @ X0 @ X5 @ X4 @ X3)
% 0.59/0.80           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 0.59/0.80              (k1_enumset1 @ X5 @ X4 @ X3)))),
% 0.59/0.80      inference('sup+', [status(thm)], ['27', '28'])).
% 0.59/0.80  thf('30', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.81         ((k2_xboole_0 @ (k2_tarski @ X3 @ X3) @ 
% 0.59/0.81           (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.59/0.81           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X3 @ X3) @ 
% 0.59/0.81              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.59/0.81      inference('sup+', [status(thm)], ['12', '29'])).
% 0.59/0.81  thf('31', plain,
% 0.59/0.81      (![X47 : $i]: ((k2_tarski @ X47 @ X47) = (k1_tarski @ X47))),
% 0.59/0.81      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.59/0.81  thf('32', plain,
% 0.59/0.81      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.59/0.81         ((k3_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24)
% 0.59/0.81           = (k2_xboole_0 @ (k1_tarski @ X20) @ 
% 0.59/0.81              (k2_enumset1 @ X21 @ X22 @ X23 @ X24)))),
% 0.59/0.81      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.59/0.81  thf('33', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.59/0.81         ((k3_enumset1 @ X0 @ X4 @ X3 @ X2 @ X1)
% 0.59/0.81           = (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ 
% 0.59/0.81              (k2_enumset1 @ X4 @ X3 @ X2 @ X1)))),
% 0.59/0.81      inference('sup+', [status(thm)], ['31', '32'])).
% 0.59/0.81  thf('34', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X0))),
% 0.59/0.81      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.59/0.81  thf('35', plain,
% 0.59/0.81      (![X47 : $i]: ((k2_tarski @ X47 @ X47) = (k1_tarski @ X47))),
% 0.59/0.81      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.59/0.81  thf('36', plain,
% 0.59/0.81      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.59/0.81         ((k2_enumset1 @ X16 @ X17 @ X18 @ X19)
% 0.59/0.81           = (k2_xboole_0 @ (k1_tarski @ X16) @ (k1_enumset1 @ X17 @ X18 @ X19)))),
% 0.59/0.81      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.59/0.81  thf('37', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.81         ((k2_enumset1 @ X0 @ X3 @ X2 @ X1)
% 0.59/0.81           = (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ 
% 0.59/0.81              (k1_enumset1 @ X3 @ X2 @ X1)))),
% 0.59/0.81      inference('sup+', [status(thm)], ['35', '36'])).
% 0.59/0.81  thf('38', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.81         ((k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0)
% 0.59/0.81           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.59/0.81      inference('demod', [status(thm)], ['30', '33', '34', '37'])).
% 0.59/0.81  thf('39', plain,
% 0.59/0.81      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.59/0.81         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.59/0.81      inference('demod', [status(thm)], ['0', '38'])).
% 0.59/0.81  thf('40', plain, ($false), inference('simplify', [status(thm)], ['39'])).
% 0.59/0.81  
% 0.59/0.81  % SZS output end Refutation
% 0.59/0.81  
% 0.59/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
