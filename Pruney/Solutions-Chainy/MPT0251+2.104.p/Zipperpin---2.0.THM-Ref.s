%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.u00sOeDgE8

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:15 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 134 expanded)
%              Number of leaves         :   22 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :  455 ( 899 expanded)
%              Number of equality atoms :   58 ( 116 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('0',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ ( k4_xboole_0 @ X11 @ X12 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('10',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(t46_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t46_zfmisc_1])).

thf('15',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l31_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('16',plain,(
    ! [X47: $i,X48: $i] :
      ( ( ( k3_xboole_0 @ X48 @ ( k1_tarski @ X47 ) )
        = ( k1_tarski @ X47 ) )
      | ~ ( r2_hidden @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('17',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('19',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ X0 )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) )
      = ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','21'])).

thf('23',plain,
    ( k1_xboole_0
    = ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['13','22'])).

thf('24',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('27',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('28',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('33',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('38',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ ( k4_xboole_0 @ X11 @ X12 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','42'])).

thf('44',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','43'])).

thf('45',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('46',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['46','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.u00sOeDgE8
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:53:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 100 iterations in 0.044s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(t21_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      (![X6 : $i, X7 : $i]:
% 0.20/0.50         ((k3_xboole_0 @ X6 @ (k2_xboole_0 @ X6 @ X7)) = (X6))),
% 0.20/0.50      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.20/0.50  thf(t51_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.20/0.50       ( A ) ))).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (![X11 : $i, X12 : $i]:
% 0.20/0.50         ((k2_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ (k4_xboole_0 @ X11 @ X12))
% 0.20/0.50           = (X11))),
% 0.20/0.50      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))
% 0.20/0.50           = (X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['0', '1'])).
% 0.20/0.50  thf(t46_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X9 : $i, X10 : $i]:
% 0.20/0.50         ((k4_xboole_0 @ X9 @ (k2_xboole_0 @ X9 @ X10)) = (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.20/0.50  thf('4', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X6 : $i, X7 : $i]:
% 0.20/0.50         ((k3_xboole_0 @ X6 @ (k2_xboole_0 @ X6 @ X7)) = (X6))),
% 0.20/0.50      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.20/0.50  thf('6', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['4', '5'])).
% 0.20/0.50  thf(t100_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X2 : $i, X3 : $i]:
% 0.20/0.50         ((k4_xboole_0 @ X2 @ X3)
% 0.20/0.50           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['6', '7'])).
% 0.20/0.50  thf('9', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X9 : $i, X10 : $i]:
% 0.20/0.50         ((k4_xboole_0 @ X9 @ (k2_xboole_0 @ X9 @ X10)) = (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.20/0.50  thf('11', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['9', '10'])).
% 0.20/0.50  thf('12', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['8', '11'])).
% 0.20/0.50  thf('13', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['8', '11'])).
% 0.20/0.50  thf(t98_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X17 : $i, X18 : $i]:
% 0.20/0.50         ((k2_xboole_0 @ X17 @ X18)
% 0.20/0.50           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.20/0.50  thf(t46_zfmisc_1, conjecture,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r2_hidden @ A @ B ) =>
% 0.20/0.50       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i]:
% 0.20/0.50        ( ( r2_hidden @ A @ B ) =>
% 0.20/0.50          ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t46_zfmisc_1])).
% 0.20/0.50  thf('15', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(l31_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r2_hidden @ A @ B ) =>
% 0.20/0.50       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (![X47 : $i, X48 : $i]:
% 0.20/0.50         (((k3_xboole_0 @ X48 @ (k1_tarski @ X47)) = (k1_tarski @ X47))
% 0.20/0.50          | ~ (r2_hidden @ X47 @ X48))),
% 0.20/0.50      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X2 : $i, X3 : $i]:
% 0.20/0.50         ((k4_xboole_0 @ X2 @ X3)
% 0.20/0.50           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.20/0.50         = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['17', '18'])).
% 0.20/0.50  thf(t91_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.50       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.50         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 0.20/0.50           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ X0)
% 0.20/0.50           = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['19', '20'])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.20/0.50           (k4_xboole_0 @ X0 @ (k1_tarski @ sk_A)))
% 0.20/0.50           = (k5_xboole_0 @ sk_B @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['14', '21'])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (((k1_xboole_0)
% 0.20/0.50         = (k5_xboole_0 @ sk_B @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['13', '22'])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.50         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 0.20/0.50           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.20/0.50           = (k5_xboole_0 @ sk_B @ 
% 0.20/0.50              (k5_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ X0)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['23', '24'])).
% 0.20/0.50  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.50  thf(t17_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i]: (r1_tarski @ (k3_xboole_0 @ X4 @ X5) @ X4)),
% 0.20/0.50      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.20/0.50  thf(t3_xboole_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (![X8 : $i]: (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['26', '29'])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (![X2 : $i, X3 : $i]:
% 0.20/0.50         ((k4_xboole_0 @ X2 @ X3)
% 0.20/0.50           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['30', '31'])).
% 0.20/0.50  thf(t5_boole, axiom,
% 0.20/0.50    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.50  thf('33', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [t5_boole])).
% 0.20/0.50  thf('34', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['32', '33'])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      (![X17 : $i, X18 : $i]:
% 0.20/0.50         ((k2_xboole_0 @ X17 @ X18)
% 0.20/0.50           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['34', '35'])).
% 0.20/0.50  thf('37', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['32', '33'])).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      (![X11 : $i, X12 : $i]:
% 0.20/0.50         ((k2_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ (k4_xboole_0 @ X11 @ X12))
% 0.20/0.50           = (X11))),
% 0.20/0.50      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X0) = (X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['37', '38'])).
% 0.20/0.50  thf('40', plain,
% 0.20/0.50      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['26', '29'])).
% 0.20/0.50  thf('41', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['39', '40'])).
% 0.20/0.50  thf('42', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['36', '41'])).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((X0)
% 0.20/0.50           = (k5_xboole_0 @ sk_B @ 
% 0.20/0.50              (k5_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ X0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['25', '42'])).
% 0.20/0.50  thf('44', plain,
% 0.20/0.50      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.20/0.50         = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['12', '43'])).
% 0.20/0.50  thf('45', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [t5_boole])).
% 0.20/0.50  thf('46', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['44', '45'])).
% 0.20/0.50  thf('47', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (sk_B))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('48', plain, ($false),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['46', '47'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
