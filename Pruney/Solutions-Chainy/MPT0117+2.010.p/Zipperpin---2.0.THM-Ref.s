%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jZoocWqkG1

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:48 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 134 expanded)
%              Number of leaves         :   20 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :  397 ( 910 expanded)
%              Number of equality atoms :   36 (  98 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t110_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ C @ B ) )
       => ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t110_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('3',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ sk_B_1 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k2_xboole_0 @ X33 @ X34 )
      = ( k5_xboole_0 @ X33 @ ( k4_xboole_0 @ X34 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X27: $i] :
      ( ( k5_xboole_0 @ X27 @ X27 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ X26 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('9',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ k1_xboole_0 )
      = X23 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','11'])).

thf('13',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_C_1 )
    = ( k5_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['3','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,
    ( sk_C_1
    = ( k5_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,
    ( sk_C_1
    = ( k3_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['17','20'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('22',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X21 @ X22 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_tarski @ X16 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_C_1 @ X0 ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('26',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('28',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','11'])).

thf('30',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_A )
    = ( k5_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('32',plain,
    ( sk_A
    = ( k5_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('34',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf(t97_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
        & ( r1_tarski @ ( k4_xboole_0 @ B @ A ) @ C ) )
     => ( r1_tarski @ ( k5_xboole_0 @ A @ B ) @ C ) ) )).

thf('37',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( r1_tarski @ ( k5_xboole_0 @ X30 @ X31 ) @ X32 )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X31 @ X30 ) @ X32 )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X30 @ X31 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[t97_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_A ) @ sk_B_1 )
      | ( r1_tarski @ ( k5_xboole_0 @ X0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_C_1 @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['25','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('41',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['0','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jZoocWqkG1
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:53:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.76/0.95  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.76/0.95  % Solved by: fo/fo7.sh
% 0.76/0.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.95  % done 1217 iterations in 0.446s
% 0.76/0.95  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.76/0.95  % SZS output start Refutation
% 0.76/0.95  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.76/0.95  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.95  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.76/0.95  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.76/0.95  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.76/0.95  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.95  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.76/0.95  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.76/0.95  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.76/0.95  thf(t110_xboole_1, conjecture,
% 0.76/0.95    (![A:$i,B:$i,C:$i]:
% 0.76/0.95     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.76/0.95       ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 0.76/0.95  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.95    (~( ![A:$i,B:$i,C:$i]:
% 0.76/0.95        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.76/0.95          ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )),
% 0.76/0.95    inference('cnf.neg', [status(esa)], [t110_xboole_1])).
% 0.76/0.95  thf('0', plain, (~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ sk_B_1)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('1', plain, ((r1_tarski @ sk_C_1 @ sk_B_1)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf(t12_xboole_1, axiom,
% 0.76/0.95    (![A:$i,B:$i]:
% 0.76/0.95     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.76/0.95  thf('2', plain,
% 0.76/0.95      (![X11 : $i, X12 : $i]:
% 0.76/0.95         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 0.76/0.95      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.76/0.95  thf('3', plain, (((k2_xboole_0 @ sk_C_1 @ sk_B_1) = (sk_B_1))),
% 0.76/0.95      inference('sup-', [status(thm)], ['1', '2'])).
% 0.76/0.95  thf(t98_xboole_1, axiom,
% 0.76/0.95    (![A:$i,B:$i]:
% 0.76/0.95     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.76/0.95  thf('4', plain,
% 0.76/0.95      (![X33 : $i, X34 : $i]:
% 0.76/0.95         ((k2_xboole_0 @ X33 @ X34)
% 0.76/0.95           = (k5_xboole_0 @ X33 @ (k4_xboole_0 @ X34 @ X33)))),
% 0.76/0.95      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.76/0.95  thf(t92_xboole_1, axiom,
% 0.76/0.95    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.76/0.95  thf('5', plain, (![X27 : $i]: ((k5_xboole_0 @ X27 @ X27) = (k1_xboole_0))),
% 0.76/0.95      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.76/0.95  thf(t91_xboole_1, axiom,
% 0.76/0.95    (![A:$i,B:$i,C:$i]:
% 0.76/0.95     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.76/0.95       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.76/0.95  thf('6', plain,
% 0.76/0.95      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.76/0.95         ((k5_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ X26)
% 0.76/0.95           = (k5_xboole_0 @ X24 @ (k5_xboole_0 @ X25 @ X26)))),
% 0.76/0.95      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.76/0.95  thf('7', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.76/0.95           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.76/0.95      inference('sup+', [status(thm)], ['5', '6'])).
% 0.76/0.95  thf(commutativity_k5_xboole_0, axiom,
% 0.76/0.95    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.76/0.95  thf('8', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.76/0.95      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.76/0.95  thf(t5_boole, axiom,
% 0.76/0.95    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.76/0.95  thf('9', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ k1_xboole_0) = (X23))),
% 0.76/0.95      inference('cnf', [status(esa)], [t5_boole])).
% 0.76/0.95  thf('10', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.76/0.95      inference('sup+', [status(thm)], ['8', '9'])).
% 0.76/0.95  thf('11', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.76/0.95      inference('demod', [status(thm)], ['7', '10'])).
% 0.76/0.95  thf('12', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k4_xboole_0 @ X0 @ X1)
% 0.76/0.95           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.76/0.95      inference('sup+', [status(thm)], ['4', '11'])).
% 0.76/0.95  thf('13', plain,
% 0.76/0.95      (((k4_xboole_0 @ sk_B_1 @ sk_C_1) = (k5_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.76/0.95      inference('sup+', [status(thm)], ['3', '12'])).
% 0.76/0.95  thf('14', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.76/0.95      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.76/0.95  thf('15', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.76/0.95      inference('demod', [status(thm)], ['7', '10'])).
% 0.76/0.95  thf('16', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.76/0.95      inference('sup+', [status(thm)], ['14', '15'])).
% 0.76/0.95  thf('17', plain,
% 0.76/0.95      (((sk_C_1) = (k5_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 0.76/0.95      inference('sup+', [status(thm)], ['13', '16'])).
% 0.76/0.95  thf(t100_xboole_1, axiom,
% 0.76/0.95    (![A:$i,B:$i]:
% 0.76/0.95     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.76/0.95  thf('18', plain,
% 0.76/0.95      (![X9 : $i, X10 : $i]:
% 0.76/0.95         ((k4_xboole_0 @ X9 @ X10)
% 0.76/0.95           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.76/0.95      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.76/0.95  thf('19', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.76/0.95      inference('demod', [status(thm)], ['7', '10'])).
% 0.76/0.95  thf('20', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k3_xboole_0 @ X1 @ X0)
% 0.76/0.95           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.76/0.95      inference('sup+', [status(thm)], ['18', '19'])).
% 0.76/0.95  thf('21', plain, (((sk_C_1) = (k3_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.76/0.95      inference('demod', [status(thm)], ['17', '20'])).
% 0.76/0.95  thf(t36_xboole_1, axiom,
% 0.76/0.95    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.76/0.95  thf('22', plain,
% 0.76/0.95      (![X21 : $i, X22 : $i]: (r1_tarski @ (k4_xboole_0 @ X21 @ X22) @ X21)),
% 0.76/0.95      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.76/0.95  thf(t18_xboole_1, axiom,
% 0.76/0.95    (![A:$i,B:$i,C:$i]:
% 0.76/0.95     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 0.76/0.95  thf('23', plain,
% 0.76/0.95      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.76/0.95         ((r1_tarski @ X16 @ X17)
% 0.76/0.95          | ~ (r1_tarski @ X16 @ (k3_xboole_0 @ X17 @ X18)))),
% 0.76/0.95      inference('cnf', [status(esa)], [t18_xboole_1])).
% 0.76/0.95  thf('24', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.95         (r1_tarski @ (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2) @ X1)),
% 0.76/0.95      inference('sup-', [status(thm)], ['22', '23'])).
% 0.76/0.95  thf('25', plain,
% 0.76/0.95      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_C_1 @ X0) @ sk_B_1)),
% 0.76/0.95      inference('sup+', [status(thm)], ['21', '24'])).
% 0.76/0.95  thf('26', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('27', plain,
% 0.76/0.95      (![X11 : $i, X12 : $i]:
% 0.76/0.95         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 0.76/0.95      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.76/0.95  thf('28', plain, (((k2_xboole_0 @ sk_A @ sk_B_1) = (sk_B_1))),
% 0.76/0.95      inference('sup-', [status(thm)], ['26', '27'])).
% 0.76/0.95  thf('29', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k4_xboole_0 @ X0 @ X1)
% 0.76/0.95           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.76/0.95      inference('sup+', [status(thm)], ['4', '11'])).
% 0.76/0.95  thf('30', plain,
% 0.76/0.95      (((k4_xboole_0 @ sk_B_1 @ sk_A) = (k5_xboole_0 @ sk_A @ sk_B_1))),
% 0.76/0.95      inference('sup+', [status(thm)], ['28', '29'])).
% 0.76/0.95  thf('31', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.76/0.95      inference('sup+', [status(thm)], ['14', '15'])).
% 0.76/0.95  thf('32', plain,
% 0.76/0.95      (((sk_A) = (k5_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.76/0.95      inference('sup+', [status(thm)], ['30', '31'])).
% 0.76/0.95  thf('33', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k3_xboole_0 @ X1 @ X0)
% 0.76/0.95           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.76/0.95      inference('sup+', [status(thm)], ['18', '19'])).
% 0.76/0.95  thf('34', plain, (((sk_A) = (k3_xboole_0 @ sk_B_1 @ sk_A))),
% 0.76/0.95      inference('demod', [status(thm)], ['32', '33'])).
% 0.76/0.95  thf('35', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.95         (r1_tarski @ (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2) @ X1)),
% 0.76/0.95      inference('sup-', [status(thm)], ['22', '23'])).
% 0.76/0.95  thf('36', plain,
% 0.76/0.95      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_A @ X0) @ sk_B_1)),
% 0.76/0.95      inference('sup+', [status(thm)], ['34', '35'])).
% 0.76/0.95  thf(t97_xboole_1, axiom,
% 0.76/0.95    (![A:$i,B:$i,C:$i]:
% 0.76/0.95     ( ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) & 
% 0.76/0.95         ( r1_tarski @ ( k4_xboole_0 @ B @ A ) @ C ) ) =>
% 0.76/0.95       ( r1_tarski @ ( k5_xboole_0 @ A @ B ) @ C ) ))).
% 0.76/0.95  thf('37', plain,
% 0.76/0.95      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.76/0.95         ((r1_tarski @ (k5_xboole_0 @ X30 @ X31) @ X32)
% 0.76/0.95          | ~ (r1_tarski @ (k4_xboole_0 @ X31 @ X30) @ X32)
% 0.76/0.95          | ~ (r1_tarski @ (k4_xboole_0 @ X30 @ X31) @ X32))),
% 0.76/0.95      inference('cnf', [status(esa)], [t97_xboole_1])).
% 0.76/0.95  thf('38', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         (~ (r1_tarski @ (k4_xboole_0 @ X0 @ sk_A) @ sk_B_1)
% 0.76/0.95          | (r1_tarski @ (k5_xboole_0 @ X0 @ sk_A) @ sk_B_1))),
% 0.76/0.95      inference('sup-', [status(thm)], ['36', '37'])).
% 0.76/0.95  thf('39', plain, ((r1_tarski @ (k5_xboole_0 @ sk_C_1 @ sk_A) @ sk_B_1)),
% 0.76/0.95      inference('sup-', [status(thm)], ['25', '38'])).
% 0.76/0.95  thf('40', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.76/0.95      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.76/0.95  thf('41', plain, ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ sk_B_1)),
% 0.76/0.95      inference('demod', [status(thm)], ['39', '40'])).
% 0.76/0.95  thf('42', plain, ($false), inference('demod', [status(thm)], ['0', '41'])).
% 0.76/0.95  
% 0.76/0.95  % SZS output end Refutation
% 0.76/0.95  
% 0.76/0.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
