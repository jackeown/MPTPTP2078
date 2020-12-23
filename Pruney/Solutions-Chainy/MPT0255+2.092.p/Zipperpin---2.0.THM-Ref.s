%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.P1Sv9zLShr

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:07 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 343 expanded)
%              Number of leaves         :   23 ( 121 expanded)
%              Depth                    :   14
%              Number of atoms          :  371 (2075 expanded)
%              Number of equality atoms :   61 ( 333 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('2',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('3',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('4',plain,
    ( k1_xboole_0
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( k1_xboole_0
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X50 @ X51 ) )
      = ( k2_xboole_0 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('7',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
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
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) )
      = X9 ) ),
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

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('14',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    k1_xboole_0 = sk_A ),
    inference(demod,[status(thm)],['11','12','15'])).

thf('17',plain,
    ( k1_xboole_0
    = ( k2_tarski @ k1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['4','16'])).

thf('18',plain,
    ( k1_xboole_0
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('19',plain,(
    k1_xboole_0 = sk_A ),
    inference(demod,[status(thm)],['11','12','15'])).

thf('20',plain,
    ( k1_xboole_0
    = ( k2_xboole_0 @ k1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

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
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('24',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('26',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['20','31'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('33',plain,(
    ! [X22: $i] :
      ( ( k2_tarski @ X22 @ X22 )
      = ( k1_tarski @ X22 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('34',plain,
    ( k1_xboole_0
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','32','33'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('35',plain,(
    ! [X52: $i,X53: $i] :
      ( ( X53 != X52 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X53 ) @ ( k1_tarski @ X52 ) )
       != ( k1_tarski @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('36',plain,(
    ! [X52: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X52 ) @ ( k1_tarski @ X52 ) )
     != ( k1_tarski @ X52 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) @ k1_xboole_0 )
 != ( k1_tarski @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,
    ( k1_xboole_0
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','32','33'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('40',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( k1_xboole_0
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','32','33'])).

thf('45',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['37','38','43','44'])).

thf('46',plain,(
    $false ),
    inference(simplify,[status(thm)],['45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.P1Sv9zLShr
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:53:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 85 iterations in 0.036s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.19/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.48  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.19/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.48  thf(t50_zfmisc_1, conjecture,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.48        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 0.19/0.48  thf('0', plain,
% 0.19/0.48      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t21_xboole_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.19/0.48  thf('1', plain,
% 0.19/0.48      (![X9 : $i, X10 : $i]:
% 0.19/0.48         ((k3_xboole_0 @ X9 @ (k2_xboole_0 @ X9 @ X10)) = (X9))),
% 0.19/0.48      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.19/0.48  thf('2', plain,
% 0.19/0.48      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0)
% 0.19/0.48         = (k2_tarski @ sk_A @ sk_B))),
% 0.19/0.48      inference('sup+', [status(thm)], ['0', '1'])).
% 0.19/0.48  thf(t2_boole, axiom,
% 0.19/0.48    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      (![X11 : $i]: ((k3_xboole_0 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [t2_boole])).
% 0.19/0.48  thf('4', plain, (((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B))),
% 0.19/0.48      inference('demod', [status(thm)], ['2', '3'])).
% 0.19/0.48  thf('5', plain, (((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B))),
% 0.19/0.48      inference('demod', [status(thm)], ['2', '3'])).
% 0.19/0.48  thf(l51_zfmisc_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.19/0.48  thf('6', plain,
% 0.19/0.48      (![X50 : $i, X51 : $i]:
% 0.19/0.48         ((k3_tarski @ (k2_tarski @ X50 @ X51)) = (k2_xboole_0 @ X50 @ X51))),
% 0.19/0.48      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.19/0.48  thf('7', plain, (((k3_tarski @ k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.19/0.48      inference('sup+', [status(thm)], ['5', '6'])).
% 0.19/0.48  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.19/0.48  thf('8', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.19/0.48  thf('9', plain, (((k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.19/0.48      inference('demod', [status(thm)], ['7', '8'])).
% 0.19/0.48  thf('10', plain,
% 0.19/0.48      (![X9 : $i, X10 : $i]:
% 0.19/0.48         ((k3_xboole_0 @ X9 @ (k2_xboole_0 @ X9 @ X10)) = (X9))),
% 0.19/0.48      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.19/0.48  thf('11', plain, (((k3_xboole_0 @ sk_A @ k1_xboole_0) = (sk_A))),
% 0.19/0.48      inference('sup+', [status(thm)], ['9', '10'])).
% 0.19/0.48  thf(commutativity_k3_xboole_0, axiom,
% 0.19/0.48    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.19/0.48  thf('12', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.48      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.48  thf('13', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.48      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.48  thf('14', plain,
% 0.19/0.48      (![X11 : $i]: ((k3_xboole_0 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [t2_boole])).
% 0.19/0.48  thf('15', plain,
% 0.19/0.48      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.19/0.48      inference('sup+', [status(thm)], ['13', '14'])).
% 0.19/0.48  thf('16', plain, (((k1_xboole_0) = (sk_A))),
% 0.19/0.48      inference('demod', [status(thm)], ['11', '12', '15'])).
% 0.19/0.48  thf('17', plain, (((k1_xboole_0) = (k2_tarski @ k1_xboole_0 @ sk_B))),
% 0.19/0.48      inference('demod', [status(thm)], ['4', '16'])).
% 0.19/0.48  thf('18', plain, (((k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.19/0.48      inference('demod', [status(thm)], ['7', '8'])).
% 0.19/0.48  thf('19', plain, (((k1_xboole_0) = (sk_A))),
% 0.19/0.48      inference('demod', [status(thm)], ['11', '12', '15'])).
% 0.19/0.48  thf('20', plain, (((k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ sk_B))),
% 0.19/0.48      inference('demod', [status(thm)], ['18', '19'])).
% 0.19/0.48  thf(commutativity_k5_xboole_0, axiom,
% 0.19/0.48    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.19/0.48  thf('21', plain,
% 0.19/0.48      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.19/0.48      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.19/0.48  thf(t5_boole, axiom,
% 0.19/0.48    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.19/0.48  thf('22', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.19/0.48      inference('cnf', [status(esa)], [t5_boole])).
% 0.19/0.48  thf('23', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.19/0.48      inference('sup+', [status(thm)], ['21', '22'])).
% 0.19/0.48  thf(t94_xboole_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( k2_xboole_0 @ A @ B ) =
% 0.19/0.48       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.48  thf('24', plain,
% 0.19/0.48      (![X20 : $i, X21 : $i]:
% 0.19/0.48         ((k2_xboole_0 @ X20 @ X21)
% 0.19/0.48           = (k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ 
% 0.19/0.48              (k3_xboole_0 @ X20 @ X21)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.19/0.48  thf('25', plain,
% 0.19/0.48      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.19/0.48      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.19/0.48  thf('26', plain,
% 0.19/0.48      (![X20 : $i, X21 : $i]:
% 0.19/0.48         ((k2_xboole_0 @ X20 @ X21)
% 0.19/0.48           = (k5_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ 
% 0.19/0.48              (k5_xboole_0 @ X20 @ X21)))),
% 0.19/0.48      inference('demod', [status(thm)], ['24', '25'])).
% 0.19/0.48  thf('27', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.19/0.48           = (k5_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0) @ X0))),
% 0.19/0.48      inference('sup+', [status(thm)], ['23', '26'])).
% 0.19/0.48  thf('28', plain,
% 0.19/0.48      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.19/0.48      inference('sup+', [status(thm)], ['13', '14'])).
% 0.19/0.48  thf('29', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.19/0.48      inference('demod', [status(thm)], ['27', '28'])).
% 0.19/0.48  thf('30', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.19/0.48      inference('sup+', [status(thm)], ['21', '22'])).
% 0.19/0.48  thf('31', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.19/0.48      inference('sup+', [status(thm)], ['29', '30'])).
% 0.19/0.48  thf('32', plain, (((k1_xboole_0) = (sk_B))),
% 0.19/0.48      inference('demod', [status(thm)], ['20', '31'])).
% 0.19/0.48  thf(t69_enumset1, axiom,
% 0.19/0.48    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.48  thf('33', plain,
% 0.19/0.48      (![X22 : $i]: ((k2_tarski @ X22 @ X22) = (k1_tarski @ X22))),
% 0.19/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.48  thf('34', plain, (((k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.19/0.48      inference('demod', [status(thm)], ['17', '32', '33'])).
% 0.19/0.48  thf(t20_zfmisc_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.19/0.48         ( k1_tarski @ A ) ) <=>
% 0.19/0.48       ( ( A ) != ( B ) ) ))).
% 0.19/0.48  thf('35', plain,
% 0.19/0.48      (![X52 : $i, X53 : $i]:
% 0.19/0.48         (((X53) != (X52))
% 0.19/0.48          | ((k4_xboole_0 @ (k1_tarski @ X53) @ (k1_tarski @ X52))
% 0.19/0.48              != (k1_tarski @ X53)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.19/0.48  thf('36', plain,
% 0.19/0.48      (![X52 : $i]:
% 0.19/0.48         ((k4_xboole_0 @ (k1_tarski @ X52) @ (k1_tarski @ X52))
% 0.19/0.48           != (k1_tarski @ X52))),
% 0.19/0.48      inference('simplify', [status(thm)], ['35'])).
% 0.19/0.48  thf('37', plain,
% 0.19/0.48      (((k4_xboole_0 @ (k1_tarski @ k1_xboole_0) @ k1_xboole_0)
% 0.19/0.48         != (k1_tarski @ k1_xboole_0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['34', '36'])).
% 0.19/0.48  thf('38', plain, (((k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.19/0.48      inference('demod', [status(thm)], ['17', '32', '33'])).
% 0.19/0.48  thf('39', plain,
% 0.19/0.48      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.19/0.48      inference('sup+', [status(thm)], ['13', '14'])).
% 0.19/0.48  thf(t100_xboole_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.48  thf('40', plain,
% 0.19/0.48      (![X5 : $i, X6 : $i]:
% 0.19/0.48         ((k4_xboole_0 @ X5 @ X6)
% 0.19/0.48           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.19/0.48  thf('41', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.19/0.48           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.19/0.48      inference('sup+', [status(thm)], ['39', '40'])).
% 0.19/0.48  thf('42', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.19/0.48      inference('cnf', [status(esa)], [t5_boole])).
% 0.19/0.48  thf('43', plain,
% 0.19/0.48      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.19/0.48      inference('demod', [status(thm)], ['41', '42'])).
% 0.19/0.48  thf('44', plain, (((k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.19/0.48      inference('demod', [status(thm)], ['17', '32', '33'])).
% 0.19/0.48  thf('45', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.19/0.48      inference('demod', [status(thm)], ['37', '38', '43', '44'])).
% 0.19/0.48  thf('46', plain, ($false), inference('simplify', [status(thm)], ['45'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
