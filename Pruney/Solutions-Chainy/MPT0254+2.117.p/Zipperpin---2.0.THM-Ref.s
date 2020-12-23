%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YYmwjGpVQG

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:50 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 126 expanded)
%              Number of leaves         :   25 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :  420 ( 761 expanded)
%              Number of equality atoms :   58 ( 107 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t49_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t49_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

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
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
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
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','8'])).

thf('10',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('13',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('15',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
    = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('19',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('21',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['20','27'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('29',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['15','34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('38',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ X31 @ X32 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X31 ) @ X32 )
       != ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('40',plain,(
    ! [X25: $i] :
      ( ( k2_tarski @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('41',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( X20 != X19 )
      | ( r2_hidden @ X20 @ X21 )
      | ( X21
       != ( k2_tarski @ X22 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('42',plain,(
    ! [X19: $i,X22: $i] :
      ( r2_hidden @ X19 @ ( k2_tarski @ X22 @ X19 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['39','43'])).

thf('45',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','44'])).

thf('46',plain,(
    $false ),
    inference(simplify,[status(thm)],['45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YYmwjGpVQG
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:38:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 210 iterations in 0.061s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.52  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.52  thf(t49_zfmisc_1, conjecture,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i,B:$i]:
% 0.22/0.52        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t49_zfmisc_1])).
% 0.22/0.52  thf('0', plain,
% 0.22/0.52      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t98_xboole_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      (![X17 : $i, X18 : $i]:
% 0.22/0.52         ((k2_xboole_0 @ X17 @ X18)
% 0.22/0.52           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.22/0.52  thf(t92_xboole_1, axiom,
% 0.22/0.52    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.52  thf('2', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.22/0.52      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.22/0.52  thf(t91_xboole_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.22/0.52       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.22/0.52  thf('3', plain,
% 0.22/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.52         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.22/0.52           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.22/0.52           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['2', '3'])).
% 0.22/0.52  thf(commutativity_k5_xboole_0, axiom,
% 0.22/0.52    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.22/0.52  thf('5', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.22/0.52      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.22/0.52  thf(t5_boole, axiom,
% 0.22/0.52    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.52  thf('6', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.22/0.52      inference('cnf', [status(esa)], [t5_boole])).
% 0.22/0.52  thf('7', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['5', '6'])).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.22/0.52      inference('demod', [status(thm)], ['4', '7'])).
% 0.22/0.52  thf('9', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((k4_xboole_0 @ X0 @ X1)
% 0.22/0.52           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['1', '8'])).
% 0.22/0.52  thf('10', plain,
% 0.22/0.52      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.22/0.52         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['0', '9'])).
% 0.22/0.52  thf('11', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.22/0.52      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.22/0.52  thf('12', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['5', '6'])).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.22/0.52  thf(t39_xboole_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.52  thf('14', plain,
% 0.22/0.52      (![X10 : $i, X11 : $i]:
% 0.22/0.52         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 0.22/0.52           = (k2_xboole_0 @ X10 @ X11))),
% 0.22/0.52      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.22/0.52         = (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.22/0.52      inference('sup+', [status(thm)], ['13', '14'])).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      (![X17 : $i, X18 : $i]:
% 0.22/0.52         ((k2_xboole_0 @ X17 @ X18)
% 0.22/0.52           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.22/0.52  thf('17', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['5', '6'])).
% 0.22/0.52  thf('18', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['16', '17'])).
% 0.22/0.52  thf(t36_xboole_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 0.22/0.52      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.22/0.52  thf('20', plain,
% 0.22/0.52      (![X0 : $i]: (r1_tarski @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ X0)),
% 0.22/0.52      inference('sup+', [status(thm)], ['18', '19'])).
% 0.22/0.52  thf(t2_boole, axiom,
% 0.22/0.52    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.52  thf('21', plain,
% 0.22/0.52      (![X7 : $i]: ((k3_xboole_0 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.52      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.52  thf(t100_xboole_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.52  thf('22', plain,
% 0.22/0.52      (![X5 : $i, X6 : $i]:
% 0.22/0.52         ((k4_xboole_0 @ X5 @ X6)
% 0.22/0.52           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['21', '22'])).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['16', '17'])).
% 0.22/0.52  thf('25', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.52      inference('demod', [status(thm)], ['23', '24'])).
% 0.22/0.52  thf('26', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.22/0.52      inference('cnf', [status(esa)], [t5_boole])).
% 0.22/0.52  thf('27', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['25', '26'])).
% 0.22/0.52  thf('28', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.22/0.52      inference('demod', [status(thm)], ['20', '27'])).
% 0.22/0.52  thf(l32_xboole_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.52  thf('29', plain,
% 0.22/0.52      (![X2 : $i, X4 : $i]:
% 0.22/0.52         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.22/0.52      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.22/0.52  thf('30', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.52  thf('31', plain,
% 0.22/0.52      (![X17 : $i, X18 : $i]:
% 0.22/0.52         ((k2_xboole_0 @ X17 @ X18)
% 0.22/0.52           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.22/0.52  thf('32', plain,
% 0.22/0.52      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['30', '31'])).
% 0.22/0.52  thf('33', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.22/0.52      inference('cnf', [status(esa)], [t5_boole])).
% 0.22/0.52  thf('34', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.22/0.52      inference('demod', [status(thm)], ['32', '33'])).
% 0.22/0.52  thf('35', plain,
% 0.22/0.52      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('36', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.22/0.52      inference('demod', [status(thm)], ['15', '34', '35'])).
% 0.22/0.52  thf('37', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.52  thf(l33_zfmisc_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.22/0.52       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.22/0.52  thf('38', plain,
% 0.22/0.52      (![X31 : $i, X32 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X31 @ X32)
% 0.22/0.52          | ((k4_xboole_0 @ (k1_tarski @ X31) @ X32) != (k1_tarski @ X31)))),
% 0.22/0.52      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.22/0.52  thf('39', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.22/0.52          | ~ (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.52  thf(t69_enumset1, axiom,
% 0.22/0.52    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.52  thf('40', plain,
% 0.22/0.52      (![X25 : $i]: ((k2_tarski @ X25 @ X25) = (k1_tarski @ X25))),
% 0.22/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.52  thf(d2_tarski, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.22/0.52       ( ![D:$i]:
% 0.22/0.52         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.22/0.52  thf('41', plain,
% 0.22/0.52      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.52         (((X20) != (X19))
% 0.22/0.52          | (r2_hidden @ X20 @ X21)
% 0.22/0.52          | ((X21) != (k2_tarski @ X22 @ X19)))),
% 0.22/0.52      inference('cnf', [status(esa)], [d2_tarski])).
% 0.22/0.52  thf('42', plain,
% 0.22/0.52      (![X19 : $i, X22 : $i]: (r2_hidden @ X19 @ (k2_tarski @ X22 @ X19))),
% 0.22/0.52      inference('simplify', [status(thm)], ['41'])).
% 0.22/0.52  thf('43', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['40', '42'])).
% 0.22/0.52  thf('44', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.22/0.52      inference('demod', [status(thm)], ['39', '43'])).
% 0.22/0.52  thf('45', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['36', '44'])).
% 0.22/0.52  thf('46', plain, ($false), inference('simplify', [status(thm)], ['45'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
