%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aj2J3psDbx

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:00 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 148 expanded)
%              Number of leaves         :   22 (  55 expanded)
%              Depth                    :   15
%              Number of atoms          :  565 (1299 expanded)
%              Number of equality atoms :   72 ( 163 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X55: $i,X56: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X55 @ X56 ) )
      = ( k2_xboole_0 @ X55 @ X56 ) ) ),
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
    ! [X61: $i,X62: $i] :
      ( ( ( k5_xboole_0 @ ( k1_tarski @ X61 ) @ ( k1_tarski @ X62 ) )
        = ( k2_tarski @ X61 @ X62 ) )
      | ( X61 = X62 ) ) ),
    inference(cnf,[status(esa)],[t29_zfmisc_1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('4',plain,(
    ! [X25: $i] :
      ( ( k2_tarski @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('5',plain,(
    ! [X25: $i] :
      ( ( k2_tarski @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('6',plain,(
    ! [X61: $i,X62: $i] :
      ( ( ( k5_xboole_0 @ ( k1_tarski @ X61 ) @ ( k1_tarski @ X62 ) )
        = ( k2_tarski @ X61 @ X62 ) )
      | ( X61 = X62 ) ) ),
    inference(cnf,[status(esa)],[t29_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) )
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X1 = X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X25: $i] :
      ( ( k2_tarski @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t19_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k1_tarski @ A ) ) )).

thf('9',plain,(
    ! [X57: $i,X58: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X57 ) @ ( k2_tarski @ X57 @ X58 ) )
      = ( k1_tarski @ X57 ) ) ),
    inference(cnf,[status(esa)],[t19_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X4 @ X6 ) @ ( k3_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

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
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) )
        = ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( X1 = X0 ) ) ),
    inference('sup+',[status(thm)],['7','18'])).

thf('20',plain,(
    ! [X57: $i,X58: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X57 ) @ ( k2_tarski @ X57 @ X58 ) )
      = ( k1_tarski @ X57 ) ) ),
    inference(cnf,[status(esa)],[t19_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) )
        = ( k1_tarski @ X1 ) )
      | ( X1 = X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ X1 ) )
      | ( X1 = X0 ) ) ),
    inference('sup+',[status(thm)],['4','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('24',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('25',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k5_xboole_0 @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('26',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['22','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X1 = X0 )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['3','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('34',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X25: $i] :
      ( ( k2_tarski @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = k1_xboole_0 ) )).

thf('37',plain,(
    ! [X59: $i,X60: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X59 ) @ ( k2_tarski @ X59 @ X60 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t22_zfmisc_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k5_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('40',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X25: $i] :
      ( ( k2_tarski @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('44',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['34'])).

thf('45',plain,(
    ! [X25: $i] :
      ( ( k2_tarski @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('46',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['2','35','42','43','44','45'])).

thf('47',plain,(
    $false ),
    inference(simplify,[status(thm)],['46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aj2J3psDbx
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:00:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.40/1.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.40/1.59  % Solved by: fo/fo7.sh
% 1.40/1.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.40/1.59  % done 1586 iterations in 1.135s
% 1.40/1.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.40/1.59  % SZS output start Refutation
% 1.40/1.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.40/1.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.40/1.59  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.40/1.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.40/1.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.40/1.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.40/1.59  thf(sk_A_type, type, sk_A: $i).
% 1.40/1.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.40/1.59  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.40/1.59  thf(sk_B_type, type, sk_B: $i).
% 1.40/1.59  thf(t32_zfmisc_1, conjecture,
% 1.40/1.59    (![A:$i,B:$i]:
% 1.40/1.59     ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 1.40/1.59       ( k2_tarski @ A @ B ) ))).
% 1.40/1.59  thf(zf_stmt_0, negated_conjecture,
% 1.40/1.59    (~( ![A:$i,B:$i]:
% 1.40/1.59        ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 1.40/1.59          ( k2_tarski @ A @ B ) ) )),
% 1.40/1.59    inference('cnf.neg', [status(esa)], [t32_zfmisc_1])).
% 1.40/1.59  thf('0', plain,
% 1.40/1.59      (((k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 1.40/1.59         != (k2_tarski @ sk_A @ sk_B))),
% 1.40/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.59  thf(l51_zfmisc_1, axiom,
% 1.40/1.59    (![A:$i,B:$i]:
% 1.40/1.59     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.40/1.59  thf('1', plain,
% 1.40/1.59      (![X55 : $i, X56 : $i]:
% 1.40/1.59         ((k3_tarski @ (k2_tarski @ X55 @ X56)) = (k2_xboole_0 @ X55 @ X56))),
% 1.40/1.59      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.40/1.59  thf('2', plain,
% 1.40/1.59      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 1.40/1.59         != (k2_tarski @ sk_A @ sk_B))),
% 1.40/1.59      inference('demod', [status(thm)], ['0', '1'])).
% 1.40/1.59  thf(t29_zfmisc_1, axiom,
% 1.40/1.59    (![A:$i,B:$i]:
% 1.40/1.59     ( ( ( A ) != ( B ) ) =>
% 1.40/1.59       ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 1.40/1.59         ( k2_tarski @ A @ B ) ) ))).
% 1.40/1.59  thf('3', plain,
% 1.40/1.59      (![X61 : $i, X62 : $i]:
% 1.40/1.59         (((k5_xboole_0 @ (k1_tarski @ X61) @ (k1_tarski @ X62))
% 1.40/1.59            = (k2_tarski @ X61 @ X62))
% 1.40/1.59          | ((X61) = (X62)))),
% 1.40/1.59      inference('cnf', [status(esa)], [t29_zfmisc_1])).
% 1.40/1.59  thf(t69_enumset1, axiom,
% 1.40/1.59    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.40/1.59  thf('4', plain, (![X25 : $i]: ((k2_tarski @ X25 @ X25) = (k1_tarski @ X25))),
% 1.40/1.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.40/1.59  thf('5', plain, (![X25 : $i]: ((k2_tarski @ X25 @ X25) = (k1_tarski @ X25))),
% 1.40/1.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.40/1.59  thf('6', plain,
% 1.40/1.59      (![X61 : $i, X62 : $i]:
% 1.40/1.59         (((k5_xboole_0 @ (k1_tarski @ X61) @ (k1_tarski @ X62))
% 1.40/1.59            = (k2_tarski @ X61 @ X62))
% 1.40/1.59          | ((X61) = (X62)))),
% 1.40/1.59      inference('cnf', [status(esa)], [t29_zfmisc_1])).
% 1.40/1.59  thf('7', plain,
% 1.40/1.59      (![X0 : $i, X1 : $i]:
% 1.40/1.59         (((k5_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0))
% 1.40/1.59            = (k2_tarski @ X1 @ X0))
% 1.40/1.59          | ((X1) = (X0)))),
% 1.40/1.59      inference('sup+', [status(thm)], ['5', '6'])).
% 1.40/1.59  thf('8', plain, (![X25 : $i]: ((k2_tarski @ X25 @ X25) = (k1_tarski @ X25))),
% 1.40/1.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.40/1.59  thf(t19_zfmisc_1, axiom,
% 1.40/1.59    (![A:$i,B:$i]:
% 1.40/1.59     ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 1.40/1.59       ( k1_tarski @ A ) ))).
% 1.40/1.59  thf('9', plain,
% 1.40/1.59      (![X57 : $i, X58 : $i]:
% 1.40/1.59         ((k3_xboole_0 @ (k1_tarski @ X57) @ (k2_tarski @ X57 @ X58))
% 1.40/1.59           = (k1_tarski @ X57))),
% 1.40/1.59      inference('cnf', [status(esa)], [t19_zfmisc_1])).
% 1.40/1.59  thf('10', plain,
% 1.40/1.59      (![X0 : $i]:
% 1.40/1.59         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 1.40/1.59           = (k1_tarski @ X0))),
% 1.40/1.59      inference('sup+', [status(thm)], ['8', '9'])).
% 1.40/1.59  thf(t112_xboole_1, axiom,
% 1.40/1.59    (![A:$i,B:$i,C:$i]:
% 1.40/1.59     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 1.40/1.59       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 1.40/1.59  thf('11', plain,
% 1.40/1.59      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.40/1.59         ((k5_xboole_0 @ (k3_xboole_0 @ X4 @ X6) @ (k3_xboole_0 @ X5 @ X6))
% 1.40/1.59           = (k3_xboole_0 @ (k5_xboole_0 @ X4 @ X5) @ X6))),
% 1.40/1.59      inference('cnf', [status(esa)], [t112_xboole_1])).
% 1.40/1.59  thf('12', plain,
% 1.40/1.59      (![X0 : $i, X1 : $i]:
% 1.40/1.59         ((k5_xboole_0 @ (k1_tarski @ X0) @ 
% 1.40/1.59           (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 1.40/1.59           = (k3_xboole_0 @ (k5_xboole_0 @ (k1_tarski @ X0) @ X1) @ 
% 1.40/1.59              (k1_tarski @ X0)))),
% 1.40/1.59      inference('sup+', [status(thm)], ['10', '11'])).
% 1.40/1.59  thf(commutativity_k3_xboole_0, axiom,
% 1.40/1.59    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.40/1.59  thf('13', plain,
% 1.40/1.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.40/1.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.40/1.59  thf('14', plain,
% 1.40/1.59      (![X0 : $i, X1 : $i]:
% 1.40/1.59         ((k5_xboole_0 @ (k1_tarski @ X0) @ 
% 1.40/1.59           (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 1.40/1.59           = (k3_xboole_0 @ (k1_tarski @ X0) @ 
% 1.40/1.59              (k5_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 1.40/1.59      inference('demod', [status(thm)], ['12', '13'])).
% 1.40/1.59  thf('15', plain,
% 1.40/1.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.40/1.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.40/1.59  thf(t100_xboole_1, axiom,
% 1.40/1.59    (![A:$i,B:$i]:
% 1.40/1.59     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.40/1.59  thf('16', plain,
% 1.40/1.59      (![X2 : $i, X3 : $i]:
% 1.40/1.59         ((k4_xboole_0 @ X2 @ X3)
% 1.40/1.59           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 1.40/1.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.40/1.59  thf('17', plain,
% 1.40/1.59      (![X0 : $i, X1 : $i]:
% 1.40/1.59         ((k4_xboole_0 @ X0 @ X1)
% 1.40/1.59           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.40/1.59      inference('sup+', [status(thm)], ['15', '16'])).
% 1.40/1.59  thf('18', plain,
% 1.40/1.59      (![X0 : $i, X1 : $i]:
% 1.40/1.59         ((k4_xboole_0 @ (k1_tarski @ X0) @ X1)
% 1.40/1.59           = (k3_xboole_0 @ (k1_tarski @ X0) @ 
% 1.40/1.59              (k5_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 1.40/1.59      inference('demod', [status(thm)], ['14', '17'])).
% 1.40/1.59  thf('19', plain,
% 1.40/1.59      (![X0 : $i, X1 : $i]:
% 1.40/1.59         (((k4_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0))
% 1.40/1.59            = (k3_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0)))
% 1.40/1.59          | ((X1) = (X0)))),
% 1.40/1.59      inference('sup+', [status(thm)], ['7', '18'])).
% 1.40/1.59  thf('20', plain,
% 1.40/1.59      (![X57 : $i, X58 : $i]:
% 1.40/1.59         ((k3_xboole_0 @ (k1_tarski @ X57) @ (k2_tarski @ X57 @ X58))
% 1.40/1.59           = (k1_tarski @ X57))),
% 1.40/1.59      inference('cnf', [status(esa)], [t19_zfmisc_1])).
% 1.40/1.59  thf('21', plain,
% 1.40/1.59      (![X0 : $i, X1 : $i]:
% 1.40/1.59         (((k4_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0))
% 1.40/1.59            = (k1_tarski @ X1))
% 1.40/1.59          | ((X1) = (X0)))),
% 1.40/1.59      inference('demod', [status(thm)], ['19', '20'])).
% 1.40/1.59  thf('22', plain,
% 1.40/1.59      (![X0 : $i, X1 : $i]:
% 1.40/1.59         (((k4_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 1.40/1.59            = (k1_tarski @ X1))
% 1.40/1.59          | ((X1) = (X0)))),
% 1.40/1.59      inference('sup+', [status(thm)], ['4', '21'])).
% 1.40/1.59  thf('23', plain,
% 1.40/1.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.40/1.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.40/1.59  thf(t94_xboole_1, axiom,
% 1.40/1.59    (![A:$i,B:$i]:
% 1.40/1.59     ( ( k2_xboole_0 @ A @ B ) =
% 1.40/1.59       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.40/1.59  thf('24', plain,
% 1.40/1.59      (![X11 : $i, X12 : $i]:
% 1.40/1.59         ((k2_xboole_0 @ X11 @ X12)
% 1.40/1.59           = (k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ 
% 1.40/1.59              (k3_xboole_0 @ X11 @ X12)))),
% 1.40/1.59      inference('cnf', [status(esa)], [t94_xboole_1])).
% 1.40/1.59  thf(t91_xboole_1, axiom,
% 1.40/1.59    (![A:$i,B:$i,C:$i]:
% 1.40/1.59     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.40/1.59       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.40/1.59  thf('25', plain,
% 1.40/1.59      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.40/1.59         ((k5_xboole_0 @ (k5_xboole_0 @ X8 @ X9) @ X10)
% 1.40/1.59           = (k5_xboole_0 @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 1.40/1.59      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.40/1.59  thf('26', plain,
% 1.40/1.59      (![X11 : $i, X12 : $i]:
% 1.40/1.59         ((k2_xboole_0 @ X11 @ X12)
% 1.40/1.59           = (k5_xboole_0 @ X11 @ 
% 1.40/1.59              (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X11 @ X12))))),
% 1.40/1.59      inference('demod', [status(thm)], ['24', '25'])).
% 1.40/1.59  thf('27', plain,
% 1.40/1.59      (![X0 : $i, X1 : $i]:
% 1.40/1.59         ((k2_xboole_0 @ X0 @ X1)
% 1.40/1.59           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 1.40/1.59      inference('sup+', [status(thm)], ['23', '26'])).
% 1.40/1.59  thf('28', plain,
% 1.40/1.59      (![X2 : $i, X3 : $i]:
% 1.40/1.59         ((k4_xboole_0 @ X2 @ X3)
% 1.40/1.59           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 1.40/1.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.40/1.59  thf('29', plain,
% 1.40/1.59      (![X0 : $i, X1 : $i]:
% 1.40/1.59         ((k2_xboole_0 @ X0 @ X1)
% 1.40/1.59           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.40/1.59      inference('demod', [status(thm)], ['27', '28'])).
% 1.40/1.59  thf('30', plain,
% 1.40/1.59      (![X0 : $i, X1 : $i]:
% 1.40/1.59         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 1.40/1.59            = (k5_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))
% 1.40/1.59          | ((X0) = (X1)))),
% 1.40/1.59      inference('sup+', [status(thm)], ['22', '29'])).
% 1.40/1.59  thf('31', plain,
% 1.40/1.59      (![X0 : $i, X1 : $i]:
% 1.40/1.59         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 1.40/1.59            = (k2_tarski @ X1 @ X0))
% 1.40/1.59          | ((X1) = (X0))
% 1.40/1.59          | ((X0) = (X1)))),
% 1.40/1.59      inference('sup+', [status(thm)], ['3', '30'])).
% 1.40/1.59  thf('32', plain,
% 1.40/1.59      (![X0 : $i, X1 : $i]:
% 1.40/1.59         (((X1) = (X0))
% 1.40/1.59          | ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 1.40/1.59              = (k2_tarski @ X1 @ X0)))),
% 1.40/1.59      inference('simplify', [status(thm)], ['31'])).
% 1.40/1.59  thf('33', plain,
% 1.40/1.59      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 1.40/1.59         != (k2_tarski @ sk_A @ sk_B))),
% 1.40/1.59      inference('demod', [status(thm)], ['0', '1'])).
% 1.40/1.59  thf('34', plain,
% 1.40/1.59      ((((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))
% 1.40/1.59        | ((sk_A) = (sk_B)))),
% 1.40/1.59      inference('sup-', [status(thm)], ['32', '33'])).
% 1.40/1.59  thf('35', plain, (((sk_A) = (sk_B))),
% 1.40/1.59      inference('simplify', [status(thm)], ['34'])).
% 1.40/1.59  thf('36', plain,
% 1.40/1.59      (![X25 : $i]: ((k2_tarski @ X25 @ X25) = (k1_tarski @ X25))),
% 1.40/1.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.40/1.59  thf(t22_zfmisc_1, axiom,
% 1.40/1.59    (![A:$i,B:$i]:
% 1.40/1.59     ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 1.40/1.59       ( k1_xboole_0 ) ))).
% 1.40/1.59  thf('37', plain,
% 1.40/1.59      (![X59 : $i, X60 : $i]:
% 1.40/1.59         ((k4_xboole_0 @ (k1_tarski @ X59) @ (k2_tarski @ X59 @ X60))
% 1.40/1.59           = (k1_xboole_0))),
% 1.40/1.59      inference('cnf', [status(esa)], [t22_zfmisc_1])).
% 1.40/1.59  thf('38', plain,
% 1.40/1.59      (![X0 : $i, X1 : $i]:
% 1.40/1.59         ((k2_xboole_0 @ X0 @ X1)
% 1.40/1.59           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.40/1.59      inference('demod', [status(thm)], ['27', '28'])).
% 1.40/1.59  thf('39', plain,
% 1.40/1.59      (![X0 : $i, X1 : $i]:
% 1.40/1.59         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 1.40/1.59           = (k5_xboole_0 @ (k2_tarski @ X1 @ X0) @ k1_xboole_0))),
% 1.40/1.59      inference('sup+', [status(thm)], ['37', '38'])).
% 1.40/1.59  thf(t5_boole, axiom,
% 1.40/1.59    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.40/1.59  thf('40', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 1.40/1.59      inference('cnf', [status(esa)], [t5_boole])).
% 1.40/1.59  thf('41', plain,
% 1.40/1.59      (![X0 : $i, X1 : $i]:
% 1.40/1.59         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 1.40/1.59           = (k2_tarski @ X1 @ X0))),
% 1.40/1.59      inference('demod', [status(thm)], ['39', '40'])).
% 1.40/1.59  thf('42', plain,
% 1.40/1.59      (![X0 : $i]:
% 1.40/1.59         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 1.40/1.59           = (k2_tarski @ X0 @ X0))),
% 1.40/1.59      inference('sup+', [status(thm)], ['36', '41'])).
% 1.40/1.59  thf('43', plain,
% 1.40/1.59      (![X25 : $i]: ((k2_tarski @ X25 @ X25) = (k1_tarski @ X25))),
% 1.40/1.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.40/1.59  thf('44', plain, (((sk_A) = (sk_B))),
% 1.40/1.59      inference('simplify', [status(thm)], ['34'])).
% 1.40/1.59  thf('45', plain,
% 1.40/1.59      (![X25 : $i]: ((k2_tarski @ X25 @ X25) = (k1_tarski @ X25))),
% 1.40/1.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.40/1.59  thf('46', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 1.40/1.59      inference('demod', [status(thm)], ['2', '35', '42', '43', '44', '45'])).
% 1.40/1.59  thf('47', plain, ($false), inference('simplify', [status(thm)], ['46'])).
% 1.40/1.59  
% 1.40/1.59  % SZS output end Refutation
% 1.40/1.59  
% 1.40/1.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
