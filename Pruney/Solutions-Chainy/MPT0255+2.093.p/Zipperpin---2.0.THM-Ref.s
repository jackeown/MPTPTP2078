%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Sqr7NOpUvN

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 129 expanded)
%              Number of leaves         :   26 (  49 expanded)
%              Depth                    :   14
%              Number of atoms          :  390 ( 742 expanded)
%              Number of equality atoms :   63 ( 119 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t50_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t50_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ sk_C_1 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('2',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ k1_xboole_0 )
    = ( k2_tarski @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('3',plain,(
    ! [X14: $i] :
      ( ( k3_xboole_0 @ X14 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('4',plain,
    ( k1_xboole_0
    = ( k2_tarski @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( k1_xboole_0
    = ( k2_tarski @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X52: $i,X53: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X52 @ X53 ) )
      = ( k2_xboole_0 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('7',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('8',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('9',plain,
    ( k1_xboole_0
    = ( k2_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('11',plain,
    ( ( k3_xboole_0 @ sk_A @ k1_xboole_0 )
    = sk_A ),
    inference('sup+',[status(thm)],['9','10'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('15',plain,(
    ! [X14: $i] :
      ( ( k3_xboole_0 @ X14 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    k1_xboole_0 = sk_A ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,
    ( k1_xboole_0
    = ( k2_tarski @ k1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','17'])).

thf('19',plain,
    ( k1_xboole_0
    = ( k2_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('20',plain,(
    k1_xboole_0 = sk_A ),
    inference(demod,[status(thm)],['13','16'])).

thf('21',plain,
    ( k1_xboole_0
    = ( k2_xboole_0 @ k1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('23',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('26',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('27',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    k1_xboole_0 = sk_B_1 ),
    inference(demod,[status(thm)],['21','32'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('34',plain,(
    ! [X24: $i] :
      ( ( k2_tarski @ X24 @ X24 )
      = ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('35',plain,
    ( k1_xboole_0
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','33','34'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('36',plain,(
    ! [X54: $i,X55: $i] :
      ( ( X55 != X54 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X55 ) @ ( k1_tarski @ X54 ) )
       != ( k1_tarski @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('37',plain,(
    ! [X54: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X54 ) @ ( k1_tarski @ X54 ) )
     != ( k1_tarski @ X54 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('38',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('39',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('41',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X54: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X54 ) ) ),
    inference(demod,[status(thm)],['37','42'])).

thf('44',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','43'])).

thf('45',plain,(
    $false ),
    inference(simplify,[status(thm)],['44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Sqr7NOpUvN
% 0.15/0.36  % Computer   : n005.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 20:49:03 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 115 iterations in 0.054s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.50  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.50  thf(t50_zfmisc_1, conjecture,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.50        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ sk_C_1) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t21_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (![X12 : $i, X13 : $i]:
% 0.21/0.50         ((k3_xboole_0 @ X12 @ (k2_xboole_0 @ X12 @ X13)) = (X12))),
% 0.21/0.50      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ k1_xboole_0)
% 0.21/0.50         = (k2_tarski @ sk_A @ sk_B_1))),
% 0.21/0.50      inference('sup+', [status(thm)], ['0', '1'])).
% 0.21/0.50  thf(t2_boole, axiom,
% 0.21/0.50    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X14 : $i]: ((k3_xboole_0 @ X14 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.50  thf('4', plain, (((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B_1))),
% 0.21/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.50  thf('5', plain, (((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B_1))),
% 0.21/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.50  thf(l51_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X52 : $i, X53 : $i]:
% 0.21/0.50         ((k3_tarski @ (k2_tarski @ X52 @ X53)) = (k2_xboole_0 @ X52 @ X53))),
% 0.21/0.50      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (((k3_tarski @ k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_B_1))),
% 0.21/0.50      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.50  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.21/0.50  thf('8', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.21/0.50  thf('9', plain, (((k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_B_1))),
% 0.21/0.50      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (![X12 : $i, X13 : $i]:
% 0.21/0.50         ((k3_xboole_0 @ X12 @ (k2_xboole_0 @ X12 @ X13)) = (X12))),
% 0.21/0.50      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.21/0.50  thf('11', plain, (((k3_xboole_0 @ sk_A @ k1_xboole_0) = (sk_A))),
% 0.21/0.50      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.50  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.50  thf('13', plain, (((k3_xboole_0 @ k1_xboole_0 @ sk_A) = (sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X14 : $i]: ((k3_xboole_0 @ X14 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['14', '15'])).
% 0.21/0.50  thf('17', plain, (((k1_xboole_0) = (sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['13', '16'])).
% 0.21/0.50  thf('18', plain, (((k1_xboole_0) = (k2_tarski @ k1_xboole_0 @ sk_B_1))),
% 0.21/0.50      inference('demod', [status(thm)], ['4', '17'])).
% 0.21/0.50  thf('19', plain, (((k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_B_1))),
% 0.21/0.50      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.50  thf('20', plain, (((k1_xboole_0) = (sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['13', '16'])).
% 0.21/0.50  thf('21', plain, (((k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ sk_B_1))),
% 0.21/0.50      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.50  thf(commutativity_k5_xboole_0, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.21/0.50      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.21/0.50  thf(t5_boole, axiom,
% 0.21/0.50    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.50  thf('23', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.21/0.50      inference('cnf', [status(esa)], [t5_boole])).
% 0.21/0.50  thf('24', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['22', '23'])).
% 0.21/0.50  thf(t94_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( k2_xboole_0 @ A @ B ) =
% 0.21/0.50       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      (![X22 : $i, X23 : $i]:
% 0.21/0.50         ((k2_xboole_0 @ X22 @ X23)
% 0.21/0.50           = (k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ 
% 0.21/0.50              (k3_xboole_0 @ X22 @ X23)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.21/0.50  thf(t91_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.21/0.50       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.50         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 0.21/0.50           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      (![X22 : $i, X23 : $i]:
% 0.21/0.50         ((k2_xboole_0 @ X22 @ X23)
% 0.21/0.50           = (k5_xboole_0 @ X22 @ 
% 0.21/0.50              (k5_xboole_0 @ X23 @ (k3_xboole_0 @ X22 @ X23))))),
% 0.21/0.50      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.21/0.50           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['24', '27'])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['14', '15'])).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['28', '29'])).
% 0.21/0.50  thf('31', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.21/0.50      inference('cnf', [status(esa)], [t5_boole])).
% 0.21/0.50  thf('32', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['30', '31'])).
% 0.21/0.50  thf('33', plain, (((k1_xboole_0) = (sk_B_1))),
% 0.21/0.50      inference('demod', [status(thm)], ['21', '32'])).
% 0.21/0.50  thf(t69_enumset1, axiom,
% 0.21/0.50    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      (![X24 : $i]: ((k2_tarski @ X24 @ X24) = (k1_tarski @ X24))),
% 0.21/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.50  thf('35', plain, (((k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['18', '33', '34'])).
% 0.21/0.50  thf(t20_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.50         ( k1_tarski @ A ) ) <=>
% 0.21/0.50       ( ( A ) != ( B ) ) ))).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      (![X54 : $i, X55 : $i]:
% 0.21/0.50         (((X55) != (X54))
% 0.21/0.50          | ((k4_xboole_0 @ (k1_tarski @ X55) @ (k1_tarski @ X54))
% 0.21/0.50              != (k1_tarski @ X55)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      (![X54 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ (k1_tarski @ X54) @ (k1_tarski @ X54))
% 0.21/0.50           != (k1_tarski @ X54))),
% 0.21/0.50      inference('simplify', [status(thm)], ['36'])).
% 0.21/0.50  thf(idempotence_k3_xboole_0, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.21/0.50  thf('38', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 0.21/0.50      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.21/0.50  thf(t100_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.50  thf('39', plain,
% 0.21/0.50      (![X10 : $i, X11 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ X10 @ X11)
% 0.21/0.50           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.50  thf('40', plain,
% 0.21/0.50      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['38', '39'])).
% 0.21/0.50  thf(t92_xboole_1, axiom,
% 0.21/0.50    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.50  thf('41', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ X21) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.21/0.50  thf('42', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['40', '41'])).
% 0.21/0.50  thf('43', plain, (![X54 : $i]: ((k1_xboole_0) != (k1_tarski @ X54))),
% 0.21/0.50      inference('demod', [status(thm)], ['37', '42'])).
% 0.21/0.50  thf('44', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['35', '43'])).
% 0.21/0.50  thf('45', plain, ($false), inference('simplify', [status(thm)], ['44'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
