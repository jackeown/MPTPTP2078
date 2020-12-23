%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WNtGx7hif1

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:01 EST 2020

% Result     : Theorem 0.87s
% Output     : Refutation 0.87s
% Verified   : 
% Statistics : Number of formulae       :   58 (  93 expanded)
%              Number of leaves         :   24 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :  387 ( 745 expanded)
%              Number of equality atoms :   52 (  96 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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
    ! [X44: $i,X45: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X44 @ X45 ) )
      = ( k2_xboole_0 @ X44 @ X45 ) ) ),
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
    ! [X49: $i,X50: $i] :
      ( ( ( k5_xboole_0 @ ( k1_tarski @ X49 ) @ ( k1_tarski @ X50 ) )
        = ( k2_tarski @ X49 @ X50 ) )
      | ( X49 = X50 ) ) ),
    inference(cnf,[status(esa)],[t29_zfmisc_1])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('4',plain,(
    ! [X47: $i,X48: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X47 ) @ ( k1_tarski @ X48 ) )
        = ( k1_tarski @ X47 ) )
      | ( X47 = X48 ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
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

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('19',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
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

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('24',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['20','25'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('27',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['16'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('30',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('31',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['2','17','28','29','30'])).

thf('32',plain,(
    $false ),
    inference(simplify,[status(thm)],['31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WNtGx7hif1
% 0.14/0.36  % Computer   : n001.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 12:18:45 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.87/1.06  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.87/1.06  % Solved by: fo/fo7.sh
% 0.87/1.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.87/1.06  % done 798 iterations in 0.588s
% 0.87/1.06  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.87/1.06  % SZS output start Refutation
% 0.87/1.06  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.87/1.06  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.87/1.06  thf(sk_A_type, type, sk_A: $i).
% 0.87/1.06  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.87/1.06  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.87/1.06  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.87/1.06  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.87/1.06  thf(sk_B_type, type, sk_B: $i).
% 0.87/1.06  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.87/1.06  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.87/1.06  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.87/1.06  thf(t32_zfmisc_1, conjecture,
% 0.87/1.06    (![A:$i,B:$i]:
% 0.87/1.06     ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 0.87/1.06       ( k2_tarski @ A @ B ) ))).
% 0.87/1.06  thf(zf_stmt_0, negated_conjecture,
% 0.87/1.06    (~( ![A:$i,B:$i]:
% 0.87/1.06        ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 0.87/1.06          ( k2_tarski @ A @ B ) ) )),
% 0.87/1.06    inference('cnf.neg', [status(esa)], [t32_zfmisc_1])).
% 0.87/1.06  thf('0', plain,
% 0.87/1.06      (((k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 0.87/1.06         != (k2_tarski @ sk_A @ sk_B))),
% 0.87/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.06  thf(l51_zfmisc_1, axiom,
% 0.87/1.06    (![A:$i,B:$i]:
% 0.87/1.06     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.87/1.06  thf('1', plain,
% 0.87/1.06      (![X44 : $i, X45 : $i]:
% 0.87/1.06         ((k3_tarski @ (k2_tarski @ X44 @ X45)) = (k2_xboole_0 @ X44 @ X45))),
% 0.87/1.06      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.87/1.06  thf('2', plain,
% 0.87/1.06      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.87/1.06         != (k2_tarski @ sk_A @ sk_B))),
% 0.87/1.06      inference('demod', [status(thm)], ['0', '1'])).
% 0.87/1.06  thf(t29_zfmisc_1, axiom,
% 0.87/1.06    (![A:$i,B:$i]:
% 0.87/1.06     ( ( ( A ) != ( B ) ) =>
% 0.87/1.06       ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.87/1.06         ( k2_tarski @ A @ B ) ) ))).
% 0.87/1.06  thf('3', plain,
% 0.87/1.06      (![X49 : $i, X50 : $i]:
% 0.87/1.06         (((k5_xboole_0 @ (k1_tarski @ X49) @ (k1_tarski @ X50))
% 0.87/1.06            = (k2_tarski @ X49 @ X50))
% 0.87/1.06          | ((X49) = (X50)))),
% 0.87/1.06      inference('cnf', [status(esa)], [t29_zfmisc_1])).
% 0.87/1.06  thf(t20_zfmisc_1, axiom,
% 0.87/1.06    (![A:$i,B:$i]:
% 0.87/1.06     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.87/1.06         ( k1_tarski @ A ) ) <=>
% 0.87/1.06       ( ( A ) != ( B ) ) ))).
% 0.87/1.06  thf('4', plain,
% 0.87/1.06      (![X47 : $i, X48 : $i]:
% 0.87/1.06         (((k4_xboole_0 @ (k1_tarski @ X47) @ (k1_tarski @ X48))
% 0.87/1.06            = (k1_tarski @ X47))
% 0.87/1.06          | ((X47) = (X48)))),
% 0.87/1.06      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.87/1.06  thf(commutativity_k3_xboole_0, axiom,
% 0.87/1.06    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.87/1.06  thf('5', plain,
% 0.87/1.06      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.87/1.06      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.87/1.06  thf(t94_xboole_1, axiom,
% 0.87/1.06    (![A:$i,B:$i]:
% 0.87/1.06     ( ( k2_xboole_0 @ A @ B ) =
% 0.87/1.06       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.87/1.06  thf('6', plain,
% 0.87/1.06      (![X14 : $i, X15 : $i]:
% 0.87/1.06         ((k2_xboole_0 @ X14 @ X15)
% 0.87/1.06           = (k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ 
% 0.87/1.06              (k3_xboole_0 @ X14 @ X15)))),
% 0.87/1.06      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.87/1.06  thf(t91_xboole_1, axiom,
% 0.87/1.06    (![A:$i,B:$i,C:$i]:
% 0.87/1.06     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.87/1.06       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.87/1.06  thf('7', plain,
% 0.87/1.06      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.87/1.06         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 0.87/1.06           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 0.87/1.06      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.87/1.06  thf('8', plain,
% 0.87/1.06      (![X14 : $i, X15 : $i]:
% 0.87/1.06         ((k2_xboole_0 @ X14 @ X15)
% 0.87/1.06           = (k5_xboole_0 @ X14 @ 
% 0.87/1.06              (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X14 @ X15))))),
% 0.87/1.06      inference('demod', [status(thm)], ['6', '7'])).
% 0.87/1.06  thf('9', plain,
% 0.87/1.06      (![X0 : $i, X1 : $i]:
% 0.87/1.06         ((k2_xboole_0 @ X0 @ X1)
% 0.87/1.06           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.87/1.06      inference('sup+', [status(thm)], ['5', '8'])).
% 0.87/1.06  thf(t100_xboole_1, axiom,
% 0.87/1.06    (![A:$i,B:$i]:
% 0.87/1.06     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.87/1.06  thf('10', plain,
% 0.87/1.06      (![X6 : $i, X7 : $i]:
% 0.87/1.06         ((k4_xboole_0 @ X6 @ X7)
% 0.87/1.06           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.87/1.06      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.87/1.06  thf('11', plain,
% 0.87/1.06      (![X0 : $i, X1 : $i]:
% 0.87/1.06         ((k2_xboole_0 @ X0 @ X1)
% 0.87/1.06           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.87/1.06      inference('demod', [status(thm)], ['9', '10'])).
% 0.87/1.06  thf('12', plain,
% 0.87/1.06      (![X0 : $i, X1 : $i]:
% 0.87/1.06         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.87/1.06            = (k5_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))
% 0.87/1.06          | ((X0) = (X1)))),
% 0.87/1.06      inference('sup+', [status(thm)], ['4', '11'])).
% 0.87/1.06  thf('13', plain,
% 0.87/1.06      (![X0 : $i, X1 : $i]:
% 0.87/1.06         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.87/1.06            = (k2_tarski @ X1 @ X0))
% 0.87/1.06          | ((X1) = (X0))
% 0.87/1.06          | ((X0) = (X1)))),
% 0.87/1.06      inference('sup+', [status(thm)], ['3', '12'])).
% 0.87/1.06  thf('14', plain,
% 0.87/1.06      (![X0 : $i, X1 : $i]:
% 0.87/1.06         (((X1) = (X0))
% 0.87/1.06          | ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.87/1.06              = (k2_tarski @ X1 @ X0)))),
% 0.87/1.06      inference('simplify', [status(thm)], ['13'])).
% 0.87/1.06  thf('15', plain,
% 0.87/1.06      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.87/1.06         != (k2_tarski @ sk_A @ sk_B))),
% 0.87/1.06      inference('demod', [status(thm)], ['0', '1'])).
% 0.87/1.06  thf('16', plain,
% 0.87/1.06      ((((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))
% 0.87/1.06        | ((sk_A) = (sk_B)))),
% 0.87/1.06      inference('sup-', [status(thm)], ['14', '15'])).
% 0.87/1.06  thf('17', plain, (((sk_A) = (sk_B))),
% 0.87/1.06      inference('simplify', [status(thm)], ['16'])).
% 0.87/1.06  thf('18', plain,
% 0.87/1.06      (![X6 : $i, X7 : $i]:
% 0.87/1.06         ((k4_xboole_0 @ X6 @ X7)
% 0.87/1.06           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.87/1.06      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.87/1.06  thf('19', plain,
% 0.87/1.06      (![X14 : $i, X15 : $i]:
% 0.87/1.06         ((k2_xboole_0 @ X14 @ X15)
% 0.87/1.06           = (k5_xboole_0 @ X14 @ 
% 0.87/1.06              (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X14 @ X15))))),
% 0.87/1.06      inference('demod', [status(thm)], ['6', '7'])).
% 0.87/1.06  thf('20', plain,
% 0.87/1.06      (![X0 : $i]:
% 0.87/1.06         ((k2_xboole_0 @ X0 @ X0)
% 0.87/1.06           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.87/1.06      inference('sup+', [status(thm)], ['18', '19'])).
% 0.87/1.06  thf(idempotence_k3_xboole_0, axiom,
% 0.87/1.06    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.87/1.06  thf('21', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.87/1.06      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.87/1.06  thf(t17_xboole_1, axiom,
% 0.87/1.06    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.87/1.06  thf('22', plain,
% 0.87/1.06      (![X8 : $i, X9 : $i]: (r1_tarski @ (k3_xboole_0 @ X8 @ X9) @ X8)),
% 0.87/1.06      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.87/1.06  thf('23', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.87/1.06      inference('sup+', [status(thm)], ['21', '22'])).
% 0.87/1.06  thf(l32_xboole_1, axiom,
% 0.87/1.06    (![A:$i,B:$i]:
% 0.87/1.06     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.87/1.06  thf('24', plain,
% 0.87/1.06      (![X3 : $i, X5 : $i]:
% 0.87/1.06         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.87/1.06      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.87/1.06  thf('25', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.87/1.06      inference('sup-', [status(thm)], ['23', '24'])).
% 0.87/1.06  thf('26', plain,
% 0.87/1.06      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.87/1.06      inference('demod', [status(thm)], ['20', '25'])).
% 0.87/1.06  thf(t5_boole, axiom,
% 0.87/1.06    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.87/1.06  thf('27', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.87/1.06      inference('cnf', [status(esa)], [t5_boole])).
% 0.87/1.06  thf('28', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.87/1.06      inference('demod', [status(thm)], ['26', '27'])).
% 0.87/1.06  thf('29', plain, (((sk_A) = (sk_B))),
% 0.87/1.06      inference('simplify', [status(thm)], ['16'])).
% 0.87/1.06  thf(t69_enumset1, axiom,
% 0.87/1.06    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.87/1.06  thf('30', plain,
% 0.87/1.06      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.87/1.06      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.87/1.06  thf('31', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 0.87/1.06      inference('demod', [status(thm)], ['2', '17', '28', '29', '30'])).
% 0.87/1.06  thf('32', plain, ($false), inference('simplify', [status(thm)], ['31'])).
% 0.87/1.06  
% 0.87/1.06  % SZS output end Refutation
% 0.87/1.06  
% 0.87/1.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
