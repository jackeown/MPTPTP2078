%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kyfNRz2WTf

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:08 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 145 expanded)
%              Number of leaves         :   23 (  55 expanded)
%              Depth                    :   17
%              Number of atoms          :  450 (1006 expanded)
%              Number of equality atoms :   56 ( 123 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t13_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t13_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('2',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','14'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('16',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('18',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ~ ( r1_tarski @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
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
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['6','21','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','25'])).

thf('27',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['0','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('30',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['6','21','24'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('38',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('40',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf(t6_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf('43',plain,(
    ! [X50: $i,X51: $i] :
      ( ( X51 = X50 )
      | ~ ( r1_tarski @ ( k1_tarski @ X51 ) @ ( k1_tarski @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t6_zfmisc_1])).

thf('44',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kyfNRz2WTf
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:25:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.52/0.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.52/0.70  % Solved by: fo/fo7.sh
% 0.52/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.70  % done 494 iterations in 0.248s
% 0.52/0.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.52/0.70  % SZS output start Refutation
% 0.52/0.70  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.52/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.70  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.52/0.70  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.52/0.70  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.52/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.70  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.52/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.70  thf(t13_zfmisc_1, conjecture,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.52/0.70         ( k1_tarski @ A ) ) =>
% 0.52/0.70       ( ( A ) = ( B ) ) ))).
% 0.52/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.70    (~( ![A:$i,B:$i]:
% 0.52/0.70        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.52/0.70            ( k1_tarski @ A ) ) =>
% 0.52/0.70          ( ( A ) = ( B ) ) ) )),
% 0.52/0.70    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 0.52/0.70  thf('0', plain,
% 0.52/0.70      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.52/0.70         = (k1_tarski @ sk_A))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf(t98_xboole_1, axiom,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.52/0.70  thf('1', plain,
% 0.52/0.70      (![X20 : $i, X21 : $i]:
% 0.52/0.70         ((k2_xboole_0 @ X20 @ X21)
% 0.52/0.70           = (k5_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20)))),
% 0.52/0.70      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.52/0.70  thf(idempotence_k3_xboole_0, axiom,
% 0.52/0.70    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.52/0.70  thf('2', plain, (![X5 : $i]: ((k3_xboole_0 @ X5 @ X5) = (X5))),
% 0.52/0.70      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.52/0.70  thf(t100_xboole_1, axiom,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.52/0.70  thf('3', plain,
% 0.52/0.70      (![X6 : $i, X7 : $i]:
% 0.52/0.70         ((k4_xboole_0 @ X6 @ X7)
% 0.52/0.70           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.52/0.70      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.52/0.70  thf('4', plain,
% 0.52/0.70      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.52/0.70      inference('sup+', [status(thm)], ['2', '3'])).
% 0.52/0.70  thf(t91_xboole_1, axiom,
% 0.52/0.70    (![A:$i,B:$i,C:$i]:
% 0.52/0.70     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.52/0.70       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.52/0.70  thf('5', plain,
% 0.52/0.70      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.52/0.70         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.52/0.70           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 0.52/0.70      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.52/0.70  thf('6', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 0.52/0.70           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.52/0.70      inference('sup+', [status(thm)], ['4', '5'])).
% 0.52/0.70  thf('7', plain,
% 0.52/0.70      (![X20 : $i, X21 : $i]:
% 0.52/0.70         ((k2_xboole_0 @ X20 @ X21)
% 0.52/0.70           = (k5_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20)))),
% 0.52/0.70      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.52/0.70  thf(t36_xboole_1, axiom,
% 0.52/0.70    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.52/0.70  thf('8', plain,
% 0.52/0.70      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 0.52/0.70      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.52/0.70  thf(t28_xboole_1, axiom,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.52/0.70  thf('9', plain,
% 0.52/0.70      (![X10 : $i, X11 : $i]:
% 0.52/0.70         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.52/0.70      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.52/0.70  thf('10', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.52/0.70           = (k4_xboole_0 @ X0 @ X1))),
% 0.52/0.70      inference('sup-', [status(thm)], ['8', '9'])).
% 0.52/0.70  thf(commutativity_k3_xboole_0, axiom,
% 0.52/0.70    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.52/0.70  thf('11', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.52/0.70      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.52/0.70  thf('12', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.52/0.70           = (k4_xboole_0 @ X0 @ X1))),
% 0.52/0.70      inference('demod', [status(thm)], ['10', '11'])).
% 0.52/0.70  thf('13', plain,
% 0.52/0.70      (![X6 : $i, X7 : $i]:
% 0.52/0.70         ((k4_xboole_0 @ X6 @ X7)
% 0.52/0.70           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.52/0.70      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.52/0.70  thf('14', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.52/0.70           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.52/0.70      inference('sup+', [status(thm)], ['12', '13'])).
% 0.52/0.70  thf('15', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0))
% 0.52/0.70           = (k2_xboole_0 @ X0 @ X0))),
% 0.52/0.70      inference('sup+', [status(thm)], ['7', '14'])).
% 0.52/0.70  thf(idempotence_k2_xboole_0, axiom,
% 0.52/0.70    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.52/0.70  thf('16', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ X4) = (X4))),
% 0.52/0.70      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.52/0.70  thf('17', plain,
% 0.52/0.70      (![X0 : $i]: ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)) = (X0))),
% 0.52/0.70      inference('demod', [status(thm)], ['15', '16'])).
% 0.52/0.70  thf(t38_xboole_1, axiom,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.52/0.70       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.52/0.70  thf('18', plain,
% 0.52/0.70      (![X14 : $i, X15 : $i]:
% 0.52/0.70         (((X14) = (k1_xboole_0))
% 0.52/0.70          | ~ (r1_tarski @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.52/0.70      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.52/0.70  thf('19', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (~ (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X0)
% 0.52/0.70          | ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['17', '18'])).
% 0.52/0.70  thf('20', plain,
% 0.52/0.70      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 0.52/0.70      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.52/0.70  thf('21', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.52/0.70      inference('demod', [status(thm)], ['19', '20'])).
% 0.52/0.70  thf(commutativity_k5_xboole_0, axiom,
% 0.52/0.70    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.52/0.70  thf('22', plain,
% 0.52/0.70      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.52/0.70      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.52/0.70  thf(t5_boole, axiom,
% 0.52/0.70    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.52/0.70  thf('23', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.52/0.70      inference('cnf', [status(esa)], [t5_boole])).
% 0.52/0.70  thf('24', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.52/0.70      inference('sup+', [status(thm)], ['22', '23'])).
% 0.52/0.70  thf('25', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.52/0.70      inference('demod', [status(thm)], ['6', '21', '24'])).
% 0.52/0.70  thf('26', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         ((k4_xboole_0 @ X0 @ X1)
% 0.52/0.70           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.52/0.70      inference('sup+', [status(thm)], ['1', '25'])).
% 0.52/0.70  thf('27', plain,
% 0.52/0.70      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.52/0.70         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.52/0.70      inference('sup+', [status(thm)], ['0', '26'])).
% 0.52/0.70  thf('28', plain,
% 0.52/0.70      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.52/0.70      inference('sup+', [status(thm)], ['2', '3'])).
% 0.52/0.70  thf('29', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.52/0.70      inference('demod', [status(thm)], ['19', '20'])).
% 0.52/0.70  thf('30', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.52/0.70      inference('demod', [status(thm)], ['28', '29'])).
% 0.52/0.70  thf('31', plain,
% 0.52/0.70      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.52/0.70      inference('demod', [status(thm)], ['27', '30'])).
% 0.52/0.70  thf('32', plain,
% 0.52/0.70      (![X6 : $i, X7 : $i]:
% 0.52/0.70         ((k4_xboole_0 @ X6 @ X7)
% 0.52/0.70           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.52/0.70      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.52/0.70  thf('33', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.52/0.70      inference('demod', [status(thm)], ['6', '21', '24'])).
% 0.52/0.70  thf('34', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         ((k3_xboole_0 @ X1 @ X0)
% 0.52/0.70           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.52/0.70      inference('sup+', [status(thm)], ['32', '33'])).
% 0.52/0.70  thf('35', plain,
% 0.52/0.70      (((k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.52/0.70         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0))),
% 0.52/0.70      inference('sup+', [status(thm)], ['31', '34'])).
% 0.52/0.70  thf('36', plain,
% 0.52/0.70      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.52/0.70      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.52/0.70  thf('37', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.52/0.70      inference('sup+', [status(thm)], ['22', '23'])).
% 0.52/0.70  thf('38', plain,
% 0.52/0.70      (((k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.52/0.70         = (k1_tarski @ sk_B))),
% 0.52/0.70      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.52/0.70  thf('39', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.52/0.70      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.52/0.70  thf(t17_xboole_1, axiom,
% 0.52/0.70    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.52/0.70  thf('40', plain,
% 0.52/0.70      (![X8 : $i, X9 : $i]: (r1_tarski @ (k3_xboole_0 @ X8 @ X9) @ X8)),
% 0.52/0.70      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.52/0.70  thf('41', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.52/0.70      inference('sup+', [status(thm)], ['39', '40'])).
% 0.52/0.70  thf('42', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))),
% 0.52/0.70      inference('sup+', [status(thm)], ['38', '41'])).
% 0.52/0.70  thf(t6_zfmisc_1, axiom,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.52/0.70       ( ( A ) = ( B ) ) ))).
% 0.52/0.70  thf('43', plain,
% 0.52/0.70      (![X50 : $i, X51 : $i]:
% 0.52/0.70         (((X51) = (X50))
% 0.52/0.70          | ~ (r1_tarski @ (k1_tarski @ X51) @ (k1_tarski @ X50)))),
% 0.52/0.70      inference('cnf', [status(esa)], [t6_zfmisc_1])).
% 0.52/0.70  thf('44', plain, (((sk_B) = (sk_A))),
% 0.52/0.70      inference('sup-', [status(thm)], ['42', '43'])).
% 0.52/0.70  thf('45', plain, (((sk_A) != (sk_B))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('46', plain, ($false),
% 0.52/0.70      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 0.52/0.70  
% 0.52/0.70  % SZS output end Refutation
% 0.52/0.70  
% 0.52/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
