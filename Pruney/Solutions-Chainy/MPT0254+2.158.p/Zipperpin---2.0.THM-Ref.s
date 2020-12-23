%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.x1RSpVmK6o

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:55 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   62 (  81 expanded)
%              Number of leaves         :   21 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :  364 ( 493 expanded)
%              Number of equality atoms :   56 (  81 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X14: $i] :
      ( ( k2_tarski @ X14 @ X14 )
      = ( k1_tarski @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('1',plain,(
    ! [X47: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X47 ) )
      = X47 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X42 @ X43 ) )
      = ( k2_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k5_xboole_0 @ X5 @ ( k5_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('9',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('15',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k5_xboole_0 @ X5 @ ( k5_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('16',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','18'])).

thf('20',plain,
    ( ( k5_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['12','19'])).

thf('21',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('22',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('23',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k5_xboole_0 @ X5 @ ( k5_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','27'])).

thf(t49_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t49_zfmisc_1])).

thf('29',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t15_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ A @ B )
        = k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( ( X2 = k1_xboole_0 )
      | ( ( k2_xboole_0 @ X2 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_xboole_1])).

thf('31',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['31'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('33',plain,(
    ! [X44: $i,X45: $i] :
      ( ( X45 != X44 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X45 ) @ ( k1_tarski @ X44 ) )
       != ( k1_tarski @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('34',plain,(
    ! [X44: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X44 ) @ ( k1_tarski @ X44 ) )
     != ( k1_tarski @ X44 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ( k4_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ sk_A ) )
 != ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['31'])).

thf('37',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['31'])).

thf('38',plain,(
    ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['28','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.x1RSpVmK6o
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:28:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 56 iterations in 0.033s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.49  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.22/0.49  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(t69_enumset1, axiom,
% 0.22/0.49    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.49  thf('0', plain, (![X14 : $i]: ((k2_tarski @ X14 @ X14) = (k1_tarski @ X14))),
% 0.22/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.49  thf(t31_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.22/0.49  thf('1', plain, (![X47 : $i]: ((k3_tarski @ (k1_tarski @ X47)) = (X47))),
% 0.22/0.49      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.22/0.49  thf('2', plain, (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['0', '1'])).
% 0.22/0.49  thf(l51_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      (![X42 : $i, X43 : $i]:
% 0.22/0.49         ((k3_tarski @ (k2_tarski @ X42 @ X43)) = (k2_xboole_0 @ X42 @ X43))),
% 0.22/0.49      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.22/0.49  thf('4', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.22/0.49      inference('demod', [status(thm)], ['2', '3'])).
% 0.22/0.49  thf(t95_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( k3_xboole_0 @ A @ B ) =
% 0.22/0.49       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      (![X9 : $i, X10 : $i]:
% 0.22/0.49         ((k3_xboole_0 @ X9 @ X10)
% 0.22/0.49           = (k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ (k2_xboole_0 @ X9 @ X10)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.22/0.49  thf(t91_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.22/0.49       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.49         ((k5_xboole_0 @ (k5_xboole_0 @ X5 @ X6) @ X7)
% 0.22/0.49           = (k5_xboole_0 @ X5 @ (k5_xboole_0 @ X6 @ X7)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      (![X9 : $i, X10 : $i]:
% 0.22/0.49         ((k3_xboole_0 @ X9 @ X10)
% 0.22/0.49           = (k5_xboole_0 @ X9 @ (k5_xboole_0 @ X10 @ (k2_xboole_0 @ X9 @ X10))))),
% 0.22/0.49      inference('demod', [status(thm)], ['5', '6'])).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((k3_xboole_0 @ X0 @ X0)
% 0.22/0.49           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.22/0.49      inference('sup+', [status(thm)], ['4', '7'])).
% 0.22/0.49  thf(t92_xboole_1, axiom,
% 0.22/0.49    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.49  thf('9', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.49      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.49  thf(t5_boole, axiom,
% 0.22/0.49    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.49  thf('11', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.22/0.49      inference('cnf', [status(esa)], [t5_boole])).
% 0.22/0.49  thf('12', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.22/0.49      inference('demod', [status(thm)], ['10', '11'])).
% 0.22/0.49  thf(t100_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((k4_xboole_0 @ X0 @ X1)
% 0.22/0.49           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.49  thf('14', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.22/0.49      inference('cnf', [status(esa)], [t5_boole])).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.49         ((k5_xboole_0 @ (k5_xboole_0 @ X5 @ X6) @ X7)
% 0.22/0.49           = (k5_xboole_0 @ X5 @ (k5_xboole_0 @ X6 @ X7)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.22/0.49  thf('16', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 0.22/0.49           = (k1_xboole_0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['15', '16'])).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ X0)) = (k1_xboole_0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['14', '17'])).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((k5_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0) @ 
% 0.22/0.49           (k4_xboole_0 @ k1_xboole_0 @ X0)) = (k1_xboole_0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['13', '18'])).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      (((k5_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0))
% 0.22/0.49         = (k1_xboole_0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['12', '19'])).
% 0.22/0.49  thf('21', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.22/0.50  thf('22', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.22/0.50  thf('23', plain,
% 0.22/0.50      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.50         ((k5_xboole_0 @ (k5_xboole_0 @ X5 @ X6) @ X7)
% 0.22/0.50           = (k5_xboole_0 @ X5 @ (k5_xboole_0 @ X6 @ X7)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.22/0.50  thf('24', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.22/0.50           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.22/0.50      inference('sup+', [status(thm)], ['22', '23'])).
% 0.22/0.50  thf('25', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.50      inference('sup+', [status(thm)], ['21', '24'])).
% 0.22/0.50  thf('26', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.22/0.50      inference('cnf', [status(esa)], [t5_boole])).
% 0.22/0.50  thf('27', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.22/0.50      inference('demod', [status(thm)], ['25', '26'])).
% 0.22/0.50  thf('28', plain,
% 0.22/0.50      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('demod', [status(thm)], ['20', '27'])).
% 0.22/0.50  thf(t49_zfmisc_1, conjecture,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i,B:$i]:
% 0.22/0.50        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t49_zfmisc_1])).
% 0.22/0.50  thf('29', plain,
% 0.22/0.50      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t15_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( k2_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) =>
% 0.22/0.50       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.50  thf('30', plain,
% 0.22/0.50      (![X2 : $i, X3 : $i]:
% 0.22/0.50         (((X2) = (k1_xboole_0)) | ((k2_xboole_0 @ X2 @ X3) != (k1_xboole_0)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t15_xboole_1])).
% 0.22/0.50  thf('31', plain,
% 0.22/0.50      ((((k1_xboole_0) != (k1_xboole_0)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.50  thf('32', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.22/0.50      inference('simplify', [status(thm)], ['31'])).
% 0.22/0.50  thf(t20_zfmisc_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.22/0.50         ( k1_tarski @ A ) ) <=>
% 0.22/0.50       ( ( A ) != ( B ) ) ))).
% 0.22/0.50  thf('33', plain,
% 0.22/0.50      (![X44 : $i, X45 : $i]:
% 0.22/0.50         (((X45) != (X44))
% 0.22/0.50          | ((k4_xboole_0 @ (k1_tarski @ X45) @ (k1_tarski @ X44))
% 0.22/0.50              != (k1_tarski @ X45)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.22/0.50  thf('34', plain,
% 0.22/0.50      (![X44 : $i]:
% 0.22/0.50         ((k4_xboole_0 @ (k1_tarski @ X44) @ (k1_tarski @ X44))
% 0.22/0.50           != (k1_tarski @ X44))),
% 0.22/0.50      inference('simplify', [status(thm)], ['33'])).
% 0.22/0.50  thf('35', plain,
% 0.22/0.50      (((k4_xboole_0 @ k1_xboole_0 @ (k1_tarski @ sk_A)) != (k1_tarski @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['32', '34'])).
% 0.22/0.50  thf('36', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.22/0.50      inference('simplify', [status(thm)], ['31'])).
% 0.22/0.50  thf('37', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.22/0.50      inference('simplify', [status(thm)], ['31'])).
% 0.22/0.50  thf('38', plain,
% 0.22/0.50      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.50      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.22/0.50  thf('39', plain, ($false),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['28', '38'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
