%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CCjfsXsPDE

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:03 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 138 expanded)
%              Number of leaves         :   18 (  51 expanded)
%              Depth                    :   15
%              Number of atoms          :  404 ( 981 expanded)
%              Number of equality atoms :   61 ( 149 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t66_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
          = k1_xboole_0 )
        & ( A != k1_xboole_0 )
        & ( A
         != ( k1_tarski @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
            = k1_xboole_0 )
          & ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_zfmisc_1])).

thf('0',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('6',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','8'])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','9'])).

thf('11',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['10','11'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('18',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A )
    = ( k5_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('20',plain,
    ( ( k1_tarski @ sk_B )
    = ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('21',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('22',plain,(
    ! [X45: $i,X46: $i] :
      ( ( X46
        = ( k1_tarski @ X45 ) )
      | ( X46 = k1_xboole_0 )
      | ~ ( r1_tarski @ X46 @ ( k1_tarski @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k1_tarski @ sk_B )
    = ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('25',plain,
    ( ( ( k1_tarski @ sk_B )
      = ( k5_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_A
      = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) ) )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('30',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('31',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('34',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','32','35'])).

thf('37',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('40',plain,
    ( ( k1_tarski @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['20','38','39'])).

thf('41',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CCjfsXsPDE
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:20:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.53/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.53/0.73  % Solved by: fo/fo7.sh
% 0.53/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.73  % done 382 iterations in 0.279s
% 0.53/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.53/0.73  % SZS output start Refutation
% 0.53/0.73  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.53/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.73  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.53/0.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.53/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.73  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.53/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.73  thf(t66_zfmisc_1, conjecture,
% 0.53/0.73    (![A:$i,B:$i]:
% 0.53/0.73     ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 0.53/0.73          ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ))).
% 0.53/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.73    (~( ![A:$i,B:$i]:
% 0.53/0.73        ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 0.53/0.73             ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ) )),
% 0.53/0.73    inference('cnf.neg', [status(esa)], [t66_zfmisc_1])).
% 0.53/0.73  thf('0', plain,
% 0.53/0.73      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf(t100_xboole_1, axiom,
% 0.53/0.73    (![A:$i,B:$i]:
% 0.53/0.73     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.53/0.73  thf('1', plain,
% 0.53/0.73      (![X5 : $i, X6 : $i]:
% 0.53/0.73         ((k4_xboole_0 @ X5 @ X6)
% 0.53/0.73           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.53/0.73      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.53/0.73  thf(t92_xboole_1, axiom,
% 0.53/0.73    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.53/0.73  thf('2', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.53/0.73      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.53/0.73  thf(t91_xboole_1, axiom,
% 0.53/0.73    (![A:$i,B:$i,C:$i]:
% 0.53/0.73     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.53/0.73       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.53/0.73  thf('3', plain,
% 0.53/0.73      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.53/0.73         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.53/0.73           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.53/0.73      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.53/0.73  thf('4', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.53/0.73           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.53/0.73      inference('sup+', [status(thm)], ['2', '3'])).
% 0.53/0.73  thf(commutativity_k5_xboole_0, axiom,
% 0.53/0.73    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.53/0.73  thf('5', plain,
% 0.53/0.73      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.53/0.73      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.53/0.73  thf(t5_boole, axiom,
% 0.53/0.73    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.53/0.73  thf('6', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.53/0.73      inference('cnf', [status(esa)], [t5_boole])).
% 0.53/0.73  thf('7', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.53/0.73      inference('sup+', [status(thm)], ['5', '6'])).
% 0.53/0.73  thf('8', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.53/0.73      inference('demod', [status(thm)], ['4', '7'])).
% 0.53/0.73  thf('9', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((k3_xboole_0 @ X1 @ X0)
% 0.53/0.73           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.53/0.73      inference('sup+', [status(thm)], ['1', '8'])).
% 0.53/0.73  thf('10', plain,
% 0.53/0.73      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_B))
% 0.53/0.73         = (k5_xboole_0 @ sk_A @ k1_xboole_0))),
% 0.53/0.73      inference('sup+', [status(thm)], ['0', '9'])).
% 0.53/0.73  thf('11', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.53/0.73      inference('cnf', [status(esa)], [t5_boole])).
% 0.53/0.73  thf('12', plain, (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))),
% 0.53/0.73      inference('demod', [status(thm)], ['10', '11'])).
% 0.53/0.73  thf(commutativity_k3_xboole_0, axiom,
% 0.53/0.73    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.53/0.73  thf('13', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.53/0.73  thf('14', plain,
% 0.53/0.73      (![X5 : $i, X6 : $i]:
% 0.53/0.73         ((k4_xboole_0 @ X5 @ X6)
% 0.53/0.73           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.53/0.73      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.53/0.73  thf('15', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((k4_xboole_0 @ X0 @ X1)
% 0.53/0.73           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.53/0.73      inference('sup+', [status(thm)], ['13', '14'])).
% 0.53/0.73  thf('16', plain,
% 0.53/0.73      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_A)
% 0.53/0.73         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.53/0.73      inference('sup+', [status(thm)], ['12', '15'])).
% 0.53/0.73  thf('17', plain,
% 0.53/0.73      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.53/0.73      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.53/0.73  thf('18', plain,
% 0.53/0.73      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_A)
% 0.53/0.73         = (k5_xboole_0 @ sk_A @ (k1_tarski @ sk_B)))),
% 0.53/0.73      inference('demod', [status(thm)], ['16', '17'])).
% 0.53/0.73  thf('19', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.53/0.73      inference('demod', [status(thm)], ['4', '7'])).
% 0.53/0.73  thf('20', plain,
% 0.53/0.73      (((k1_tarski @ sk_B)
% 0.53/0.73         = (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_A)))),
% 0.53/0.73      inference('sup+', [status(thm)], ['18', '19'])).
% 0.53/0.73  thf(t36_xboole_1, axiom,
% 0.53/0.73    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.53/0.73  thf('21', plain,
% 0.53/0.73      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 0.53/0.73      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.53/0.73  thf(l3_zfmisc_1, axiom,
% 0.53/0.73    (![A:$i,B:$i]:
% 0.53/0.73     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.53/0.73       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.53/0.73  thf('22', plain,
% 0.53/0.73      (![X45 : $i, X46 : $i]:
% 0.53/0.73         (((X46) = (k1_tarski @ X45))
% 0.53/0.73          | ((X46) = (k1_xboole_0))
% 0.53/0.73          | ~ (r1_tarski @ X46 @ (k1_tarski @ X45)))),
% 0.53/0.73      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.53/0.73  thf('23', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 0.53/0.73          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0)))),
% 0.53/0.73      inference('sup-', [status(thm)], ['21', '22'])).
% 0.53/0.73  thf('24', plain,
% 0.53/0.73      (((k1_tarski @ sk_B)
% 0.53/0.73         = (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_A)))),
% 0.53/0.73      inference('sup+', [status(thm)], ['18', '19'])).
% 0.53/0.73  thf('25', plain,
% 0.53/0.73      ((((k1_tarski @ sk_B) = (k5_xboole_0 @ sk_A @ (k1_tarski @ sk_B)))
% 0.53/0.73        | ((k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))),
% 0.53/0.73      inference('sup+', [status(thm)], ['23', '24'])).
% 0.53/0.73  thf('26', plain,
% 0.53/0.73      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.53/0.73      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.53/0.73  thf('27', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.53/0.73      inference('demod', [status(thm)], ['4', '7'])).
% 0.53/0.73  thf('28', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.53/0.73      inference('sup+', [status(thm)], ['26', '27'])).
% 0.53/0.73  thf('29', plain,
% 0.53/0.73      ((((sk_A) = (k5_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B)))
% 0.53/0.73        | ((k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))),
% 0.53/0.73      inference('sup+', [status(thm)], ['25', '28'])).
% 0.53/0.73  thf(idempotence_k3_xboole_0, axiom,
% 0.53/0.73    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.53/0.73  thf('30', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 0.53/0.73      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.53/0.73  thf('31', plain,
% 0.53/0.73      (![X5 : $i, X6 : $i]:
% 0.53/0.73         ((k4_xboole_0 @ X5 @ X6)
% 0.53/0.73           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.53/0.73      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.53/0.73  thf('32', plain,
% 0.53/0.73      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.53/0.73      inference('sup+', [status(thm)], ['30', '31'])).
% 0.53/0.73  thf('33', plain,
% 0.53/0.73      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.53/0.73      inference('sup+', [status(thm)], ['30', '31'])).
% 0.53/0.73  thf('34', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.53/0.73      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.53/0.73  thf('35', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.53/0.73      inference('sup+', [status(thm)], ['33', '34'])).
% 0.53/0.73  thf('36', plain,
% 0.53/0.73      ((((sk_A) = (k1_xboole_0))
% 0.53/0.73        | ((k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))),
% 0.53/0.73      inference('demod', [status(thm)], ['29', '32', '35'])).
% 0.53/0.73  thf('37', plain, (((sk_A) != (k1_xboole_0))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('38', plain,
% 0.53/0.73      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))),
% 0.53/0.73      inference('simplify_reflect-', [status(thm)], ['36', '37'])).
% 0.53/0.73  thf('39', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.53/0.73      inference('cnf', [status(esa)], [t5_boole])).
% 0.53/0.73  thf('40', plain, (((k1_tarski @ sk_B) = (sk_A))),
% 0.53/0.73      inference('demod', [status(thm)], ['20', '38', '39'])).
% 0.53/0.73  thf('41', plain, (((sk_A) != (k1_tarski @ sk_B))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('42', plain, ($false),
% 0.53/0.73      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 0.53/0.73  
% 0.53/0.73  % SZS output end Refutation
% 0.53/0.73  
% 0.53/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
