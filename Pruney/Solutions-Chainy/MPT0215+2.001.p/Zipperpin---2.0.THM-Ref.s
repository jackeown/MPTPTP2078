%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bNnVMAko3J

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   70 (  91 expanded)
%              Number of leaves         :   22 (  36 expanded)
%              Depth                    :   12
%              Number of atoms          :  464 ( 635 expanded)
%              Number of equality atoms :   47 (  73 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t8_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k1_tarski @ A )
        = ( k2_tarski @ B @ C ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k1_tarski @ A )
          = ( k2_tarski @ B @ C ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t8_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t82_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_enumset1 @ A @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X25: $i] :
      ( ( k2_enumset1 @ X25 @ X25 @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(cnf,[status(esa)],[t82_enumset1])).

thf(t77_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_enumset1 @ A @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_enumset1 @ X23 @ X23 @ X23 @ X24 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t77_enumset1])).

thf('3',plain,(
    ! [X25: $i] :
      ( ( k2_tarski @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t137_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X15 @ X14 ) @ ( k2_tarski @ X16 @ X14 ) )
      = ( k1_enumset1 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t137_enumset1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X0 @ sk_C ) @ ( k1_tarski @ sk_A ) )
      = ( k1_enumset1 @ sk_C @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ X0 @ sk_C ) )
      = ( k1_enumset1 @ sk_C @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) )
    = ( k1_enumset1 @ sk_C @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X21 @ X21 @ X22 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('11',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_tarski @ X9 @ X8 )
      = ( k2_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['9','12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    r1_tarski @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf(t6_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf('19',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X27 = X26 )
      | ~ ( r1_tarski @ ( k1_tarski @ X27 ) @ ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t6_zfmisc_1])).

thf('20',plain,(
    sk_C = sk_A ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('22',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_enumset1 @ sk_A @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','20','21'])).

thf('23',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X21 @ X21 @ X22 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('24',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('25',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t45_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('27',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k2_enumset1 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_xboole_0 @ ( k2_tarski @ X17 @ X18 ) @ ( k2_tarski @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t45_enumset1])).

thf('28',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(l123_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ C @ A @ D ) ) )).

thf('30',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X12 @ X10 @ X11 @ X13 )
      = ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l123_enumset1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k2_enumset1 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_xboole_0 @ ( k2_tarski @ X17 @ X18 ) @ ( k2_tarski @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t45_enumset1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('34',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 )
      | ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X4 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ ( k2_tarski @ X0 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,(
    ! [X25: $i] :
      ( ( k2_tarski @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','40'])).

thf('42',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['22','41'])).

thf('43',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X27 = X26 )
      | ~ ( r1_tarski @ ( k1_tarski @ X27 ) @ ( k1_tarski @ X26 ) ) ) ),
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
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bNnVMAko3J
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:59:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 171 iterations in 0.054s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.22/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.51  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.51  thf(t8_zfmisc_1, conjecture,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( ( k1_tarski @ A ) = ( k2_tarski @ B @ C ) ) => ( ( A ) = ( B ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.51        ( ( ( k1_tarski @ A ) = ( k2_tarski @ B @ C ) ) => ( ( A ) = ( B ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t8_zfmisc_1])).
% 0.22/0.51  thf('0', plain, (((k1_tarski @ sk_A) = (k2_tarski @ sk_B @ sk_C))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(t82_enumset1, axiom,
% 0.22/0.51    (![A:$i]: ( ( k2_enumset1 @ A @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.51  thf('1', plain,
% 0.22/0.51      (![X25 : $i]: ((k2_enumset1 @ X25 @ X25 @ X25 @ X25) = (k1_tarski @ X25))),
% 0.22/0.51      inference('cnf', [status(esa)], [t82_enumset1])).
% 0.22/0.51  thf(t77_enumset1, axiom,
% 0.22/0.51    (![A:$i,B:$i]: ( ( k2_enumset1 @ A @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.22/0.51  thf('2', plain,
% 0.22/0.51      (![X23 : $i, X24 : $i]:
% 0.22/0.51         ((k2_enumset1 @ X23 @ X23 @ X23 @ X24) = (k2_tarski @ X23 @ X24))),
% 0.22/0.51      inference('cnf', [status(esa)], [t77_enumset1])).
% 0.22/0.51  thf('3', plain, (![X25 : $i]: ((k2_tarski @ X25 @ X25) = (k1_tarski @ X25))),
% 0.22/0.51      inference('demod', [status(thm)], ['1', '2'])).
% 0.22/0.51  thf('4', plain, (((k1_tarski @ sk_A) = (k2_tarski @ sk_B @ sk_C))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(t137_enumset1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 0.22/0.51       ( k1_enumset1 @ A @ B @ C ) ))).
% 0.22/0.51  thf('5', plain,
% 0.22/0.51      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.51         ((k2_xboole_0 @ (k2_tarski @ X15 @ X14) @ (k2_tarski @ X16 @ X14))
% 0.22/0.51           = (k1_enumset1 @ X14 @ X15 @ X16))),
% 0.22/0.51      inference('cnf', [status(esa)], [t137_enumset1])).
% 0.22/0.51  thf('6', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((k2_xboole_0 @ (k2_tarski @ X0 @ sk_C) @ (k1_tarski @ sk_A))
% 0.22/0.51           = (k1_enumset1 @ sk_C @ X0 @ sk_B))),
% 0.22/0.51      inference('sup+', [status(thm)], ['4', '5'])).
% 0.22/0.51  thf(commutativity_k2_xboole_0, axiom,
% 0.22/0.51    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.22/0.51  thf('7', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.51      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.22/0.51  thf('8', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ X0 @ sk_C))
% 0.22/0.51           = (k1_enumset1 @ sk_C @ X0 @ sk_B))),
% 0.22/0.51      inference('demod', [status(thm)], ['6', '7'])).
% 0.22/0.51  thf('9', plain,
% 0.22/0.51      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))
% 0.22/0.51         = (k1_enumset1 @ sk_C @ sk_C @ sk_B))),
% 0.22/0.51      inference('sup+', [status(thm)], ['3', '8'])).
% 0.22/0.51  thf(t70_enumset1, axiom,
% 0.22/0.51    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.22/0.51  thf('10', plain,
% 0.22/0.51      (![X21 : $i, X22 : $i]:
% 0.22/0.51         ((k1_enumset1 @ X21 @ X21 @ X22) = (k2_tarski @ X21 @ X22))),
% 0.22/0.51      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.51  thf(commutativity_k2_tarski, axiom,
% 0.22/0.51    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.22/0.51  thf('11', plain,
% 0.22/0.51      (![X8 : $i, X9 : $i]: ((k2_tarski @ X9 @ X8) = (k2_tarski @ X8 @ X9))),
% 0.22/0.51      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.22/0.51  thf('12', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         ((k2_tarski @ X0 @ X1) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.22/0.51      inference('sup+', [status(thm)], ['10', '11'])).
% 0.22/0.51  thf('13', plain, (((k1_tarski @ sk_A) = (k2_tarski @ sk_B @ sk_C))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('14', plain,
% 0.22/0.51      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))
% 0.22/0.51         = (k1_tarski @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['9', '12', '13'])).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.52      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.22/0.52  thf(t7_xboole_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 0.22/0.52      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.22/0.52  thf('17', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['15', '16'])).
% 0.22/0.52  thf('18', plain, ((r1_tarski @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_A))),
% 0.22/0.52      inference('sup+', [status(thm)], ['14', '17'])).
% 0.22/0.52  thf(t6_zfmisc_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.22/0.52       ( ( A ) = ( B ) ) ))).
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      (![X26 : $i, X27 : $i]:
% 0.22/0.52         (((X27) = (X26))
% 0.22/0.52          | ~ (r1_tarski @ (k1_tarski @ X27) @ (k1_tarski @ X26)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t6_zfmisc_1])).
% 0.22/0.52  thf('20', plain, (((sk_C) = (sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.52  thf('21', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((k2_tarski @ X0 @ X1) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['10', '11'])).
% 0.22/0.52  thf('22', plain, (((k1_tarski @ sk_A) = (k1_enumset1 @ sk_A @ sk_A @ sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['0', '20', '21'])).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      (![X21 : $i, X22 : $i]:
% 0.22/0.52         ((k1_enumset1 @ X21 @ X21 @ X22) = (k2_tarski @ X21 @ X22))),
% 0.22/0.52      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.52  thf(idempotence_k2_xboole_0, axiom,
% 0.22/0.52    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.22/0.52  thf('24', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.22/0.52      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.22/0.52  thf('25', plain,
% 0.22/0.52      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 0.22/0.52      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.22/0.52  thf('26', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.22/0.52      inference('sup+', [status(thm)], ['24', '25'])).
% 0.22/0.52  thf(t45_enumset1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.52     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.22/0.52       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.22/0.52  thf('27', plain,
% 0.22/0.52      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.52         ((k2_enumset1 @ X17 @ X18 @ X19 @ X20)
% 0.22/0.52           = (k2_xboole_0 @ (k2_tarski @ X17 @ X18) @ (k2_tarski @ X19 @ X20)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t45_enumset1])).
% 0.22/0.52  thf('28', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.22/0.52      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.22/0.52  thf('29', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((k2_enumset1 @ X1 @ X0 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['27', '28'])).
% 0.22/0.52  thf(l123_enumset1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.52     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ C @ A @ D ) ))).
% 0.22/0.52  thf('30', plain,
% 0.22/0.52      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.52         ((k2_enumset1 @ X12 @ X10 @ X11 @ X13)
% 0.22/0.52           = (k2_enumset1 @ X10 @ X11 @ X12 @ X13))),
% 0.22/0.52      inference('cnf', [status(esa)], [l123_enumset1])).
% 0.22/0.52  thf('31', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((k2_enumset1 @ X1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['29', '30'])).
% 0.22/0.52  thf('32', plain,
% 0.22/0.52      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.52         ((k2_enumset1 @ X17 @ X18 @ X19 @ X20)
% 0.22/0.52           = (k2_xboole_0 @ (k2_tarski @ X17 @ X18) @ (k2_tarski @ X19 @ X20)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t45_enumset1])).
% 0.22/0.52  thf('33', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.52      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.22/0.52  thf(t11_xboole_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.22/0.52  thf('34', plain,
% 0.22/0.52      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.52         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 0.22/0.52      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.22/0.52  thf('35', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.52         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2) | (r1_tarski @ X0 @ X2))),
% 0.22/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.22/0.52  thf('36', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.52         (~ (r1_tarski @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4)
% 0.22/0.52          | (r1_tarski @ (k2_tarski @ X1 @ X0) @ X4))),
% 0.22/0.52      inference('sup-', [status(thm)], ['32', '35'])).
% 0.22/0.52  thf('37', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.52         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X2)
% 0.22/0.52          | (r1_tarski @ (k2_tarski @ X0 @ X0) @ X2))),
% 0.22/0.52      inference('sup-', [status(thm)], ['31', '36'])).
% 0.22/0.52  thf('38', plain,
% 0.22/0.52      (![X25 : $i]: ((k2_tarski @ X25 @ X25) = (k1_tarski @ X25))),
% 0.22/0.52      inference('demod', [status(thm)], ['1', '2'])).
% 0.22/0.52  thf('39', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.52         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X2)
% 0.22/0.52          | (r1_tarski @ (k1_tarski @ X0) @ X2))),
% 0.22/0.52      inference('demod', [status(thm)], ['37', '38'])).
% 0.22/0.52  thf('40', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (r1_tarski @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['26', '39'])).
% 0.22/0.52  thf('41', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (r1_tarski @ (k1_tarski @ X0) @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['23', '40'])).
% 0.22/0.52  thf('42', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))),
% 0.22/0.52      inference('sup+', [status(thm)], ['22', '41'])).
% 0.22/0.52  thf('43', plain,
% 0.22/0.52      (![X26 : $i, X27 : $i]:
% 0.22/0.52         (((X27) = (X26))
% 0.22/0.52          | ~ (r1_tarski @ (k1_tarski @ X27) @ (k1_tarski @ X26)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t6_zfmisc_1])).
% 0.22/0.52  thf('44', plain, (((sk_B) = (sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['42', '43'])).
% 0.22/0.52  thf('45', plain, (((sk_A) != (sk_B))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('46', plain, ($false),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
