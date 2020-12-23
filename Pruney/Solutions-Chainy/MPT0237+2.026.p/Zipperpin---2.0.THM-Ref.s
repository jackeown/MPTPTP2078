%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zLHSR2TRNP

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:02 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 101 expanded)
%              Number of leaves         :   23 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :  409 ( 830 expanded)
%              Number of equality atoms :   57 ( 108 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X43: $i,X44: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X43 @ X44 ) )
      = ( k2_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('2',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t29_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k2_tarski @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X48: $i,X49: $i] :
      ( ( ( k5_xboole_0 @ ( k1_tarski @ X48 ) @ ( k1_tarski @ X49 ) )
        = ( k2_tarski @ X48 @ X49 ) )
      | ( X48 = X49 ) ) ),
    inference(cnf,[status(esa)],[t29_zfmisc_1])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('4',plain,(
    ! [X46: $i,X47: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X46 ) @ ( k1_tarski @ X47 ) )
        = ( k1_tarski @ X46 ) )
      | ( X46 = X47 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('8',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['4','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X1 = X0 )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['3','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('16',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['16'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('18',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k3_xboole_0 @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('19',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('21',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('22',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('25',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('29',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['16'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('32',plain,(
    ! [X15: $i] :
      ( ( k2_tarski @ X15 @ X15 )
      = ( k1_tarski @ X15 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('33',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['2','17','30','31','32'])).

thf('34',plain,(
    $false ),
    inference(simplify,[status(thm)],['33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zLHSR2TRNP
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:02:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.50/0.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.50/0.73  % Solved by: fo/fo7.sh
% 0.50/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.73  % done 499 iterations in 0.275s
% 0.50/0.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.50/0.73  % SZS output start Refutation
% 0.50/0.73  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.50/0.73  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.50/0.73  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.50/0.73  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.50/0.73  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.50/0.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.50/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.50/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.73  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.50/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.50/0.73  thf(t32_zfmisc_1, conjecture,
% 0.50/0.73    (![A:$i,B:$i]:
% 0.50/0.73     ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 0.50/0.73       ( k2_tarski @ A @ B ) ))).
% 0.50/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.73    (~( ![A:$i,B:$i]:
% 0.50/0.73        ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 0.50/0.73          ( k2_tarski @ A @ B ) ) )),
% 0.50/0.73    inference('cnf.neg', [status(esa)], [t32_zfmisc_1])).
% 0.50/0.73  thf('0', plain,
% 0.50/0.73      (((k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 0.50/0.73         != (k2_tarski @ sk_A @ sk_B))),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf(l51_zfmisc_1, axiom,
% 0.50/0.73    (![A:$i,B:$i]:
% 0.50/0.73     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.50/0.73  thf('1', plain,
% 0.50/0.73      (![X43 : $i, X44 : $i]:
% 0.50/0.73         ((k3_tarski @ (k2_tarski @ X43 @ X44)) = (k2_xboole_0 @ X43 @ X44))),
% 0.50/0.73      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.50/0.73  thf('2', plain,
% 0.50/0.73      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.50/0.73         != (k2_tarski @ sk_A @ sk_B))),
% 0.50/0.73      inference('demod', [status(thm)], ['0', '1'])).
% 0.50/0.73  thf(t29_zfmisc_1, axiom,
% 0.50/0.73    (![A:$i,B:$i]:
% 0.50/0.73     ( ( ( A ) != ( B ) ) =>
% 0.50/0.73       ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.50/0.73         ( k2_tarski @ A @ B ) ) ))).
% 0.50/0.73  thf('3', plain,
% 0.50/0.73      (![X48 : $i, X49 : $i]:
% 0.50/0.73         (((k5_xboole_0 @ (k1_tarski @ X48) @ (k1_tarski @ X49))
% 0.50/0.73            = (k2_tarski @ X48 @ X49))
% 0.50/0.73          | ((X48) = (X49)))),
% 0.50/0.73      inference('cnf', [status(esa)], [t29_zfmisc_1])).
% 0.50/0.73  thf(t20_zfmisc_1, axiom,
% 0.50/0.73    (![A:$i,B:$i]:
% 0.50/0.73     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.50/0.73         ( k1_tarski @ A ) ) <=>
% 0.50/0.73       ( ( A ) != ( B ) ) ))).
% 0.50/0.73  thf('4', plain,
% 0.50/0.73      (![X46 : $i, X47 : $i]:
% 0.50/0.73         (((k4_xboole_0 @ (k1_tarski @ X46) @ (k1_tarski @ X47))
% 0.50/0.73            = (k1_tarski @ X46))
% 0.50/0.73          | ((X46) = (X47)))),
% 0.50/0.73      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.50/0.73  thf(commutativity_k3_xboole_0, axiom,
% 0.50/0.73    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.50/0.73  thf('5', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.50/0.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.50/0.73  thf(t94_xboole_1, axiom,
% 0.50/0.73    (![A:$i,B:$i]:
% 0.50/0.73     ( ( k2_xboole_0 @ A @ B ) =
% 0.50/0.73       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.50/0.73  thf('6', plain,
% 0.50/0.73      (![X13 : $i, X14 : $i]:
% 0.50/0.73         ((k2_xboole_0 @ X13 @ X14)
% 0.50/0.73           = (k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ 
% 0.50/0.73              (k3_xboole_0 @ X13 @ X14)))),
% 0.50/0.73      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.50/0.73  thf(t91_xboole_1, axiom,
% 0.50/0.73    (![A:$i,B:$i,C:$i]:
% 0.50/0.73     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.50/0.73       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.50/0.73  thf('7', plain,
% 0.50/0.73      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.50/0.73         ((k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ X12)
% 0.50/0.73           = (k5_xboole_0 @ X10 @ (k5_xboole_0 @ X11 @ X12)))),
% 0.50/0.73      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.50/0.73  thf('8', plain,
% 0.50/0.73      (![X13 : $i, X14 : $i]:
% 0.50/0.73         ((k2_xboole_0 @ X13 @ X14)
% 0.50/0.73           = (k5_xboole_0 @ X13 @ 
% 0.50/0.73              (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X13 @ X14))))),
% 0.50/0.73      inference('demod', [status(thm)], ['6', '7'])).
% 0.50/0.73  thf('9', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i]:
% 0.50/0.73         ((k2_xboole_0 @ X0 @ X1)
% 0.50/0.73           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.50/0.73      inference('sup+', [status(thm)], ['5', '8'])).
% 0.50/0.73  thf(t100_xboole_1, axiom,
% 0.50/0.73    (![A:$i,B:$i]:
% 0.50/0.73     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.50/0.73  thf('10', plain,
% 0.50/0.73      (![X3 : $i, X4 : $i]:
% 0.50/0.73         ((k4_xboole_0 @ X3 @ X4)
% 0.50/0.73           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.50/0.73      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.50/0.73  thf('11', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i]:
% 0.50/0.73         ((k2_xboole_0 @ X0 @ X1)
% 0.50/0.73           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.50/0.73      inference('demod', [status(thm)], ['9', '10'])).
% 0.50/0.73  thf('12', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i]:
% 0.50/0.73         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.50/0.73            = (k5_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))
% 0.50/0.73          | ((X0) = (X1)))),
% 0.50/0.73      inference('sup+', [status(thm)], ['4', '11'])).
% 0.50/0.73  thf('13', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i]:
% 0.50/0.73         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.50/0.73            = (k2_tarski @ X1 @ X0))
% 0.50/0.73          | ((X1) = (X0))
% 0.50/0.73          | ((X0) = (X1)))),
% 0.50/0.73      inference('sup+', [status(thm)], ['3', '12'])).
% 0.50/0.73  thf('14', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i]:
% 0.50/0.73         (((X1) = (X0))
% 0.50/0.73          | ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.50/0.73              = (k2_tarski @ X1 @ X0)))),
% 0.50/0.73      inference('simplify', [status(thm)], ['13'])).
% 0.50/0.73  thf('15', plain,
% 0.50/0.73      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.50/0.73         != (k2_tarski @ sk_A @ sk_B))),
% 0.50/0.73      inference('demod', [status(thm)], ['0', '1'])).
% 0.50/0.73  thf('16', plain,
% 0.50/0.73      ((((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))
% 0.50/0.73        | ((sk_A) = (sk_B)))),
% 0.50/0.73      inference('sup-', [status(thm)], ['14', '15'])).
% 0.50/0.73  thf('17', plain, (((sk_A) = (sk_B))),
% 0.50/0.73      inference('simplify', [status(thm)], ['16'])).
% 0.50/0.73  thf(t21_xboole_1, axiom,
% 0.50/0.73    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.50/0.73  thf('18', plain,
% 0.50/0.73      (![X5 : $i, X6 : $i]:
% 0.50/0.73         ((k3_xboole_0 @ X5 @ (k2_xboole_0 @ X5 @ X6)) = (X5))),
% 0.50/0.73      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.50/0.73  thf('19', plain,
% 0.50/0.73      (![X3 : $i, X4 : $i]:
% 0.50/0.73         ((k4_xboole_0 @ X3 @ X4)
% 0.50/0.73           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.50/0.73      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.50/0.73  thf('20', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i]:
% 0.50/0.73         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.50/0.73           = (k5_xboole_0 @ X0 @ X0))),
% 0.50/0.73      inference('sup+', [status(thm)], ['18', '19'])).
% 0.50/0.73  thf(idempotence_k3_xboole_0, axiom,
% 0.50/0.73    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.50/0.73  thf('21', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.50/0.73      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.50/0.73  thf('22', plain,
% 0.50/0.73      (![X3 : $i, X4 : $i]:
% 0.50/0.73         ((k4_xboole_0 @ X3 @ X4)
% 0.50/0.73           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.50/0.73      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.50/0.73  thf('23', plain,
% 0.50/0.73      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.50/0.73      inference('sup+', [status(thm)], ['21', '22'])).
% 0.50/0.73  thf('24', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i]:
% 0.50/0.73         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.50/0.73           = (k4_xboole_0 @ X0 @ X0))),
% 0.50/0.73      inference('demod', [status(thm)], ['20', '23'])).
% 0.50/0.73  thf(t46_xboole_1, axiom,
% 0.50/0.73    (![A:$i,B:$i]:
% 0.50/0.73     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.50/0.73  thf('25', plain,
% 0.50/0.73      (![X7 : $i, X8 : $i]:
% 0.50/0.73         ((k4_xboole_0 @ X7 @ (k2_xboole_0 @ X7 @ X8)) = (k1_xboole_0))),
% 0.50/0.73      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.50/0.73  thf('26', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.50/0.73      inference('sup+', [status(thm)], ['24', '25'])).
% 0.50/0.73  thf('27', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i]:
% 0.50/0.73         ((k2_xboole_0 @ X0 @ X1)
% 0.50/0.73           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.50/0.73      inference('demod', [status(thm)], ['9', '10'])).
% 0.50/0.73  thf('28', plain,
% 0.50/0.73      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.50/0.73      inference('sup+', [status(thm)], ['26', '27'])).
% 0.50/0.73  thf(t5_boole, axiom,
% 0.50/0.73    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.50/0.73  thf('29', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.50/0.73      inference('cnf', [status(esa)], [t5_boole])).
% 0.50/0.73  thf('30', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.50/0.73      inference('demod', [status(thm)], ['28', '29'])).
% 0.50/0.73  thf('31', plain, (((sk_A) = (sk_B))),
% 0.50/0.73      inference('simplify', [status(thm)], ['16'])).
% 0.50/0.73  thf(t69_enumset1, axiom,
% 0.50/0.73    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.50/0.73  thf('32', plain,
% 0.50/0.73      (![X15 : $i]: ((k2_tarski @ X15 @ X15) = (k1_tarski @ X15))),
% 0.50/0.73      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.50/0.73  thf('33', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 0.50/0.73      inference('demod', [status(thm)], ['2', '17', '30', '31', '32'])).
% 0.50/0.73  thf('34', plain, ($false), inference('simplify', [status(thm)], ['33'])).
% 0.50/0.73  
% 0.50/0.73  % SZS output end Refutation
% 0.50/0.73  
% 0.50/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
