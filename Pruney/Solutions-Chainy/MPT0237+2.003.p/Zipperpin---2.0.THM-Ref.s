%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.y55LYumULc

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:58 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :   55 (  60 expanded)
%              Number of leaves         :   24 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :  482 ( 532 expanded)
%              Number of equality atoms :   42 (  47 expanded)
%              Maximal formula depth    :   18 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t32_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t32_zfmisc_1])).

thf('0',plain,(
    ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X46 @ X47 ) )
      = ( k2_xboole_0 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('2',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('3',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k2_enumset1 @ X21 @ X21 @ X22 @ X23 )
      = ( k1_enumset1 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_enumset1 @ X19 @ X19 @ X20 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('5',plain,(
    ! [X18: $i] :
      ( ( k2_tarski @ X18 @ X18 )
      = ( k1_tarski @ X18 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('8',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( k6_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 )
      = ( k5_enumset1 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('9',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( k5_enumset1 @ X33 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 )
      = ( k4_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X18: $i] :
      ( ( k2_tarski @ X18 @ X18 )
      = ( k1_tarski @ X18 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t67_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k6_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 ) @ ( k2_tarski @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t67_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('15',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k4_enumset1 @ X28 @ X28 @ X29 @ X30 @ X31 @ X32 )
      = ( k3_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('16',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k3_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27 )
      = ( k2_enumset1 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_enumset1 @ X0 @ X0 @ X0 @ X0 @ X1 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['7','17'])).

thf('19',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k4_enumset1 @ X28 @ X28 @ X29 @ X30 @ X31 @ X32 )
      = ( k3_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('20',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k3_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27 )
      = ( k2_enumset1 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X1 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf(t102_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ C @ B @ A ) ) )).

thf('22',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X9 @ X8 @ X7 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf('23',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_enumset1 @ X19 @ X19 @ X20 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k2_enumset1 @ X21 @ X21 @ X22 @ X23 )
      = ( k1_enumset1 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X1 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('27',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X6 @ X5 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('28',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','21','26','27'])).

thf('29',plain,(
    $false ),
    inference(simplify,[status(thm)],['28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.y55LYumULc
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:45:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.67/0.85  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.67/0.85  % Solved by: fo/fo7.sh
% 0.67/0.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.67/0.85  % done 898 iterations in 0.365s
% 0.67/0.85  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.67/0.85  % SZS output start Refutation
% 0.67/0.85  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.67/0.85  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.67/0.85  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.67/0.85  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.67/0.85  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.67/0.85  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.67/0.85                                           $i > $i).
% 0.67/0.85  thf(sk_B_type, type, sk_B: $i).
% 0.67/0.85  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.67/0.85  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.67/0.85  thf(sk_A_type, type, sk_A: $i).
% 0.67/0.85  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.67/0.85  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.67/0.85  thf(t32_zfmisc_1, conjecture,
% 0.67/0.85    (![A:$i,B:$i]:
% 0.67/0.85     ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 0.67/0.85       ( k2_tarski @ A @ B ) ))).
% 0.67/0.85  thf(zf_stmt_0, negated_conjecture,
% 0.67/0.85    (~( ![A:$i,B:$i]:
% 0.67/0.85        ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 0.67/0.85          ( k2_tarski @ A @ B ) ) )),
% 0.67/0.85    inference('cnf.neg', [status(esa)], [t32_zfmisc_1])).
% 0.67/0.85  thf('0', plain,
% 0.67/0.85      (((k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 0.67/0.85         != (k2_tarski @ sk_A @ sk_B))),
% 0.67/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.85  thf(l51_zfmisc_1, axiom,
% 0.67/0.85    (![A:$i,B:$i]:
% 0.67/0.85     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.67/0.85  thf('1', plain,
% 0.67/0.85      (![X46 : $i, X47 : $i]:
% 0.67/0.85         ((k3_tarski @ (k2_tarski @ X46 @ X47)) = (k2_xboole_0 @ X46 @ X47))),
% 0.67/0.85      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.67/0.85  thf('2', plain,
% 0.67/0.85      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.67/0.85         != (k2_tarski @ sk_A @ sk_B))),
% 0.67/0.85      inference('demod', [status(thm)], ['0', '1'])).
% 0.67/0.85  thf(t71_enumset1, axiom,
% 0.67/0.85    (![A:$i,B:$i,C:$i]:
% 0.67/0.85     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.67/0.85  thf('3', plain,
% 0.67/0.85      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.67/0.85         ((k2_enumset1 @ X21 @ X21 @ X22 @ X23)
% 0.67/0.85           = (k1_enumset1 @ X21 @ X22 @ X23))),
% 0.67/0.85      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.67/0.85  thf(t70_enumset1, axiom,
% 0.67/0.85    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.67/0.85  thf('4', plain,
% 0.67/0.85      (![X19 : $i, X20 : $i]:
% 0.67/0.85         ((k1_enumset1 @ X19 @ X19 @ X20) = (k2_tarski @ X19 @ X20))),
% 0.67/0.85      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.67/0.85  thf(t69_enumset1, axiom,
% 0.67/0.85    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.67/0.85  thf('5', plain, (![X18 : $i]: ((k2_tarski @ X18 @ X18) = (k1_tarski @ X18))),
% 0.67/0.85      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.67/0.85  thf('6', plain,
% 0.67/0.85      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.67/0.85      inference('sup+', [status(thm)], ['4', '5'])).
% 0.67/0.85  thf('7', plain,
% 0.67/0.85      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.67/0.85      inference('sup+', [status(thm)], ['3', '6'])).
% 0.67/0.85  thf(t75_enumset1, axiom,
% 0.67/0.85    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.67/0.85     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.67/0.85       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.67/0.85  thf('8', plain,
% 0.67/0.85      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.67/0.85         ((k6_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45)
% 0.67/0.85           = (k5_enumset1 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45))),
% 0.67/0.85      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.67/0.85  thf(t74_enumset1, axiom,
% 0.67/0.85    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.67/0.85     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.67/0.85       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.67/0.85  thf('9', plain,
% 0.67/0.85      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.67/0.85         ((k5_enumset1 @ X33 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38)
% 0.67/0.85           = (k4_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38))),
% 0.67/0.85      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.67/0.85  thf('10', plain,
% 0.67/0.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.67/0.85         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.67/0.85           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.67/0.85      inference('sup+', [status(thm)], ['8', '9'])).
% 0.67/0.85  thf('11', plain,
% 0.67/0.85      (![X18 : $i]: ((k2_tarski @ X18 @ X18) = (k1_tarski @ X18))),
% 0.67/0.85      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.67/0.85  thf(t67_enumset1, axiom,
% 0.67/0.85    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.67/0.85     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.67/0.85       ( k2_xboole_0 @
% 0.67/0.85         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ))).
% 0.67/0.85  thf('12', plain,
% 0.67/0.85      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, 
% 0.67/0.85         X17 : $i]:
% 0.67/0.85         ((k6_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17)
% 0.67/0.85           = (k2_xboole_0 @ 
% 0.67/0.85              (k4_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15) @ 
% 0.67/0.85              (k2_tarski @ X16 @ X17)))),
% 0.67/0.85      inference('cnf', [status(esa)], [t67_enumset1])).
% 0.67/0.85  thf('13', plain,
% 0.67/0.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.67/0.85         ((k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 0.67/0.85           = (k2_xboole_0 @ (k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 0.67/0.85              (k1_tarski @ X0)))),
% 0.67/0.85      inference('sup+', [status(thm)], ['11', '12'])).
% 0.67/0.85  thf('14', plain,
% 0.67/0.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.67/0.85         ((k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 0.67/0.85           = (k2_xboole_0 @ (k4_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1) @ 
% 0.67/0.85              (k1_tarski @ X0)))),
% 0.67/0.85      inference('sup+', [status(thm)], ['10', '13'])).
% 0.67/0.85  thf(t73_enumset1, axiom,
% 0.67/0.85    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.67/0.85     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.67/0.85       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.67/0.85  thf('15', plain,
% 0.67/0.85      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.67/0.85         ((k4_enumset1 @ X28 @ X28 @ X29 @ X30 @ X31 @ X32)
% 0.67/0.85           = (k3_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32))),
% 0.67/0.85      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.67/0.85  thf(t72_enumset1, axiom,
% 0.67/0.85    (![A:$i,B:$i,C:$i,D:$i]:
% 0.67/0.85     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.67/0.85  thf('16', plain,
% 0.67/0.85      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.67/0.85         ((k3_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27)
% 0.67/0.85           = (k2_enumset1 @ X24 @ X25 @ X26 @ X27))),
% 0.67/0.85      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.67/0.85  thf('17', plain,
% 0.67/0.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.67/0.85         ((k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 0.67/0.85           = (k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ 
% 0.67/0.85              (k1_tarski @ X0)))),
% 0.67/0.85      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.67/0.85  thf('18', plain,
% 0.67/0.85      (![X0 : $i, X1 : $i]:
% 0.67/0.85         ((k4_enumset1 @ X0 @ X0 @ X0 @ X0 @ X1 @ X1)
% 0.67/0.85           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.67/0.85      inference('sup+', [status(thm)], ['7', '17'])).
% 0.67/0.85  thf('19', plain,
% 0.67/0.85      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.67/0.85         ((k4_enumset1 @ X28 @ X28 @ X29 @ X30 @ X31 @ X32)
% 0.67/0.85           = (k3_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32))),
% 0.67/0.85      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.67/0.85  thf('20', plain,
% 0.67/0.85      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.67/0.85         ((k3_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27)
% 0.67/0.85           = (k2_enumset1 @ X24 @ X25 @ X26 @ X27))),
% 0.67/0.85      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.67/0.85  thf('21', plain,
% 0.67/0.85      (![X0 : $i, X1 : $i]:
% 0.67/0.85         ((k2_enumset1 @ X0 @ X0 @ X1 @ X1)
% 0.67/0.85           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.67/0.85      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.67/0.85  thf(t102_enumset1, axiom,
% 0.67/0.85    (![A:$i,B:$i,C:$i]:
% 0.67/0.85     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ C @ B @ A ) ))).
% 0.67/0.85  thf('22', plain,
% 0.67/0.85      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.67/0.85         ((k1_enumset1 @ X9 @ X8 @ X7) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 0.67/0.85      inference('cnf', [status(esa)], [t102_enumset1])).
% 0.67/0.85  thf('23', plain,
% 0.67/0.85      (![X19 : $i, X20 : $i]:
% 0.67/0.85         ((k1_enumset1 @ X19 @ X19 @ X20) = (k2_tarski @ X19 @ X20))),
% 0.67/0.85      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.67/0.85  thf('24', plain,
% 0.67/0.85      (![X0 : $i, X1 : $i]:
% 0.67/0.85         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.67/0.85      inference('sup+', [status(thm)], ['22', '23'])).
% 0.67/0.85  thf('25', plain,
% 0.67/0.85      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.67/0.85         ((k2_enumset1 @ X21 @ X21 @ X22 @ X23)
% 0.67/0.85           = (k1_enumset1 @ X21 @ X22 @ X23))),
% 0.67/0.85      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.67/0.85  thf('26', plain,
% 0.67/0.85      (![X0 : $i, X1 : $i]:
% 0.67/0.85         ((k2_enumset1 @ X0 @ X0 @ X1 @ X1) = (k2_tarski @ X1 @ X0))),
% 0.67/0.85      inference('sup+', [status(thm)], ['24', '25'])).
% 0.67/0.85  thf(commutativity_k2_tarski, axiom,
% 0.67/0.85    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.67/0.85  thf('27', plain,
% 0.67/0.85      (![X5 : $i, X6 : $i]: ((k2_tarski @ X6 @ X5) = (k2_tarski @ X5 @ X6))),
% 0.67/0.85      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.67/0.85  thf('28', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.67/0.85      inference('demod', [status(thm)], ['2', '21', '26', '27'])).
% 0.67/0.85  thf('29', plain, ($false), inference('simplify', [status(thm)], ['28'])).
% 0.67/0.85  
% 0.67/0.85  % SZS output end Refutation
% 0.67/0.85  
% 0.67/0.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
