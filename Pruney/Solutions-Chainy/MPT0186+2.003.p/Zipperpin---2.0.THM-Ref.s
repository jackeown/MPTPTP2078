%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gf23mSn0qk

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:03 EST 2020

% Result     : Theorem 1.04s
% Output     : Refutation 1.04s
% Verified   : 
% Statistics : Number of formulae       :   59 (  91 expanded)
%              Number of leaves         :   23 (  39 expanded)
%              Depth                    :   13
%              Number of atoms          :  606 (1004 expanded)
%              Number of equality atoms :   45 (  77 expanded)
%              Maximal formula depth    :   18 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(t104_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ C @ B @ D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_enumset1 @ A @ B @ C @ D )
        = ( k2_enumset1 @ A @ C @ B @ D ) ) ),
    inference('cnf.neg',[status(esa)],[t104_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_C @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( k3_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 )
      = ( k2_enumset1 @ X21 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k2_enumset1 @ X18 @ X18 @ X19 @ X20 )
      = ( k1_enumset1 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('6',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k2_enumset1 @ X18 @ X18 @ X19 @ X20 )
      = ( k1_enumset1 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t50_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_enumset1 @ X16 @ X16 @ X17 )
      = ( k2_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['4','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X2 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t66_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_enumset1 @ F @ G @ H ) ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k6_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 ) @ ( k1_enumset1 @ X12 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t66_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X1 @ X2 @ X0 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 @ X4 @ X5 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_enumset1 @ X5 @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['3','16'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('18',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k6_enumset1 @ X36 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 )
      = ( k5_enumset1 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('19',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k5_enumset1 @ X30 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 )
      = ( k4_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('22',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k6_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 ) @ ( k1_enumset1 @ X12 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t66_enumset1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_enumset1 @ X5 @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_enumset1 @ X5 @ X4 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X2 @ X1 @ X0 @ X4 @ X5 @ X3 )
      = ( k4_enumset1 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3 ) ) ),
    inference(demod,[status(thm)],['17','20','25'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('27',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k4_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 @ X29 )
      = ( k3_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('28',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( k3_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 )
      = ( k2_enumset1 @ X21 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','32'])).

thf('34',plain,(
    $false ),
    inference(simplify,[status(thm)],['33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gf23mSn0qk
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:58:18 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.04/1.25  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.04/1.25  % Solved by: fo/fo7.sh
% 1.04/1.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.04/1.25  % done 1753 iterations in 0.802s
% 1.04/1.25  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.04/1.25  % SZS output start Refutation
% 1.04/1.25  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 1.04/1.25  thf(sk_A_type, type, sk_A: $i).
% 1.04/1.25  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 1.04/1.25                                           $i > $i).
% 1.04/1.25  thf(sk_B_type, type, sk_B: $i).
% 1.04/1.25  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.04/1.25  thf(sk_C_type, type, sk_C: $i).
% 1.04/1.25  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.04/1.25  thf(sk_D_type, type, sk_D: $i).
% 1.04/1.25  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 1.04/1.25  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.04/1.25  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 1.04/1.25  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.04/1.25  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 1.04/1.25  thf(t104_enumset1, conjecture,
% 1.04/1.25    (![A:$i,B:$i,C:$i,D:$i]:
% 1.04/1.25     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ B @ D ) ))).
% 1.04/1.25  thf(zf_stmt_0, negated_conjecture,
% 1.04/1.25    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.04/1.25        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ B @ D ) ) )),
% 1.04/1.25    inference('cnf.neg', [status(esa)], [t104_enumset1])).
% 1.04/1.25  thf('0', plain,
% 1.04/1.25      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 1.04/1.25         != (k2_enumset1 @ sk_A @ sk_C @ sk_B @ sk_D))),
% 1.04/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.25  thf(t72_enumset1, axiom,
% 1.04/1.25    (![A:$i,B:$i,C:$i,D:$i]:
% 1.04/1.25     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 1.04/1.25  thf('1', plain,
% 1.04/1.25      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 1.04/1.25         ((k3_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24)
% 1.04/1.25           = (k2_enumset1 @ X21 @ X22 @ X23 @ X24))),
% 1.04/1.25      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.04/1.25  thf(t71_enumset1, axiom,
% 1.04/1.25    (![A:$i,B:$i,C:$i]:
% 1.04/1.25     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 1.04/1.25  thf('2', plain,
% 1.04/1.25      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.04/1.25         ((k2_enumset1 @ X18 @ X18 @ X19 @ X20)
% 1.04/1.25           = (k1_enumset1 @ X18 @ X19 @ X20))),
% 1.04/1.25      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.04/1.25  thf('3', plain,
% 1.04/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.25         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 1.04/1.25      inference('sup+', [status(thm)], ['1', '2'])).
% 1.04/1.25  thf(commutativity_k2_tarski, axiom,
% 1.04/1.25    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.04/1.25  thf('4', plain,
% 1.04/1.25      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 1.04/1.25      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.04/1.25  thf('5', plain,
% 1.04/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.25         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 1.04/1.25      inference('sup+', [status(thm)], ['1', '2'])).
% 1.04/1.25  thf('6', plain,
% 1.04/1.25      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.04/1.25         ((k2_enumset1 @ X18 @ X18 @ X19 @ X20)
% 1.04/1.25           = (k1_enumset1 @ X18 @ X19 @ X20))),
% 1.04/1.25      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.04/1.25  thf(t50_enumset1, axiom,
% 1.04/1.25    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.04/1.25     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 1.04/1.25       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ))).
% 1.04/1.25  thf('7', plain,
% 1.04/1.25      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.04/1.25         ((k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6)
% 1.04/1.25           = (k2_xboole_0 @ (k2_enumset1 @ X2 @ X3 @ X4 @ X5) @ 
% 1.04/1.25              (k1_tarski @ X6)))),
% 1.04/1.25      inference('cnf', [status(esa)], [t50_enumset1])).
% 1.04/1.25  thf('8', plain,
% 1.04/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.04/1.25         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 1.04/1.25           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 1.04/1.25      inference('sup+', [status(thm)], ['6', '7'])).
% 1.04/1.25  thf('9', plain,
% 1.04/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.25         ((k1_enumset1 @ X2 @ X1 @ X0)
% 1.04/1.25           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X2 @ X1) @ (k1_tarski @ X0)))),
% 1.04/1.25      inference('sup+', [status(thm)], ['5', '8'])).
% 1.04/1.25  thf(t70_enumset1, axiom,
% 1.04/1.25    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.04/1.25  thf('10', plain,
% 1.04/1.25      (![X16 : $i, X17 : $i]:
% 1.04/1.25         ((k1_enumset1 @ X16 @ X16 @ X17) = (k2_tarski @ X16 @ X17))),
% 1.04/1.25      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.04/1.25  thf('11', plain,
% 1.04/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.25         ((k1_enumset1 @ X2 @ X1 @ X0)
% 1.04/1.25           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)))),
% 1.04/1.25      inference('demod', [status(thm)], ['9', '10'])).
% 1.04/1.25  thf('12', plain,
% 1.04/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.25         ((k1_enumset1 @ X0 @ X1 @ X2)
% 1.04/1.25           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 1.04/1.25      inference('sup+', [status(thm)], ['4', '11'])).
% 1.04/1.25  thf('13', plain,
% 1.04/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.25         ((k1_enumset1 @ X2 @ X1 @ X0)
% 1.04/1.25           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)))),
% 1.04/1.25      inference('demod', [status(thm)], ['9', '10'])).
% 1.04/1.25  thf('14', plain,
% 1.04/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.25         ((k1_enumset1 @ X1 @ X2 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 1.04/1.25      inference('sup+', [status(thm)], ['12', '13'])).
% 1.04/1.25  thf(t66_enumset1, axiom,
% 1.04/1.25    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 1.04/1.25     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 1.04/1.25       ( k2_xboole_0 @
% 1.04/1.25         ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_enumset1 @ F @ G @ H ) ) ))).
% 1.04/1.25  thf('15', plain,
% 1.04/1.25      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, 
% 1.04/1.25         X14 : $i]:
% 1.04/1.25         ((k6_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14)
% 1.04/1.25           = (k2_xboole_0 @ (k3_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11) @ 
% 1.04/1.25              (k1_enumset1 @ X12 @ X13 @ X14)))),
% 1.04/1.25      inference('cnf', [status(esa)], [t66_enumset1])).
% 1.04/1.25  thf('16', plain,
% 1.04/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 1.04/1.25         ((k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X1 @ X2 @ X0)
% 1.04/1.25           = (k2_xboole_0 @ (k3_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3) @ 
% 1.04/1.25              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 1.04/1.25      inference('sup+', [status(thm)], ['14', '15'])).
% 1.04/1.25  thf('17', plain,
% 1.04/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.04/1.25         ((k6_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 @ X4 @ X5 @ X3)
% 1.04/1.25           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 1.04/1.25              (k1_enumset1 @ X5 @ X4 @ X3)))),
% 1.04/1.25      inference('sup+', [status(thm)], ['3', '16'])).
% 1.04/1.25  thf(t75_enumset1, axiom,
% 1.04/1.25    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 1.04/1.25     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 1.04/1.25       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 1.04/1.25  thf('18', plain,
% 1.04/1.25      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 1.04/1.25         ((k6_enumset1 @ X36 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42)
% 1.04/1.25           = (k5_enumset1 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42))),
% 1.04/1.25      inference('cnf', [status(esa)], [t75_enumset1])).
% 1.04/1.25  thf(t74_enumset1, axiom,
% 1.04/1.25    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.04/1.25     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 1.04/1.25       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 1.04/1.25  thf('19', plain,
% 1.04/1.25      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.04/1.25         ((k5_enumset1 @ X30 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35)
% 1.04/1.25           = (k4_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35))),
% 1.04/1.25      inference('cnf', [status(esa)], [t74_enumset1])).
% 1.04/1.25  thf('20', plain,
% 1.04/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.04/1.25         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 1.04/1.25           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 1.04/1.25      inference('sup+', [status(thm)], ['18', '19'])).
% 1.04/1.25  thf('21', plain,
% 1.04/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.25         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 1.04/1.25      inference('sup+', [status(thm)], ['1', '2'])).
% 1.04/1.25  thf('22', plain,
% 1.04/1.25      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, 
% 1.04/1.25         X14 : $i]:
% 1.04/1.25         ((k6_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14)
% 1.04/1.25           = (k2_xboole_0 @ (k3_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11) @ 
% 1.04/1.25              (k1_enumset1 @ X12 @ X13 @ X14)))),
% 1.04/1.25      inference('cnf', [status(esa)], [t66_enumset1])).
% 1.04/1.25  thf('23', plain,
% 1.04/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.04/1.25         ((k6_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3)
% 1.04/1.25           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 1.04/1.25              (k1_enumset1 @ X5 @ X4 @ X3)))),
% 1.04/1.25      inference('sup+', [status(thm)], ['21', '22'])).
% 1.04/1.25  thf('24', plain,
% 1.04/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.04/1.25         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 1.04/1.25           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 1.04/1.25      inference('sup+', [status(thm)], ['18', '19'])).
% 1.04/1.25  thf('25', plain,
% 1.04/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.04/1.25         ((k4_enumset1 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3)
% 1.04/1.25           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 1.04/1.25              (k1_enumset1 @ X5 @ X4 @ X3)))),
% 1.04/1.25      inference('demod', [status(thm)], ['23', '24'])).
% 1.04/1.25  thf('26', plain,
% 1.04/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.04/1.25         ((k4_enumset1 @ X2 @ X1 @ X0 @ X4 @ X5 @ X3)
% 1.04/1.25           = (k4_enumset1 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3))),
% 1.04/1.25      inference('demod', [status(thm)], ['17', '20', '25'])).
% 1.04/1.25  thf(t73_enumset1, axiom,
% 1.04/1.25    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.04/1.25     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 1.04/1.25       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 1.04/1.25  thf('27', plain,
% 1.04/1.25      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.04/1.25         ((k4_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 @ X29)
% 1.04/1.25           = (k3_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29))),
% 1.04/1.25      inference('cnf', [status(esa)], [t73_enumset1])).
% 1.04/1.25  thf('28', plain,
% 1.04/1.25      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 1.04/1.25         ((k3_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24)
% 1.04/1.25           = (k2_enumset1 @ X21 @ X22 @ X23 @ X24))),
% 1.04/1.25      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.04/1.25  thf('29', plain,
% 1.04/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.04/1.25         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 1.04/1.25           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 1.04/1.25      inference('sup+', [status(thm)], ['27', '28'])).
% 1.04/1.25  thf('30', plain,
% 1.04/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.04/1.25         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 1.04/1.25           = (k2_enumset1 @ X3 @ X1 @ X2 @ X0))),
% 1.04/1.25      inference('sup+', [status(thm)], ['26', '29'])).
% 1.04/1.25  thf('31', plain,
% 1.04/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.04/1.25         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 1.04/1.25           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 1.04/1.25      inference('sup+', [status(thm)], ['27', '28'])).
% 1.04/1.25  thf('32', plain,
% 1.04/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.04/1.25         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X3 @ X1 @ X2 @ X0))),
% 1.04/1.25      inference('sup+', [status(thm)], ['30', '31'])).
% 1.04/1.25  thf('33', plain,
% 1.04/1.25      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 1.04/1.25         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 1.04/1.25      inference('demod', [status(thm)], ['0', '32'])).
% 1.04/1.25  thf('34', plain, ($false), inference('simplify', [status(thm)], ['33'])).
% 1.04/1.25  
% 1.04/1.25  % SZS output end Refutation
% 1.04/1.25  
% 1.04/1.26  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
