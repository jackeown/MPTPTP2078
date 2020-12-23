%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Xy8sb1K6ke

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:39 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 119 expanded)
%              Number of leaves         :   19 (  39 expanded)
%              Depth                    :   14
%              Number of atoms          :  436 ( 838 expanded)
%              Number of equality atoms :   47 (  83 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('0',plain,(
    ! [X35: $i,X36: $i] :
      ( r1_tarski @ X35 @ ( k2_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      | ~ ( r1_tarski @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t83_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_xboole_0 @ A @ B )
      <=> ( ( k4_xboole_0 @ A @ B )
          = A ) ) ),
    inference('cnf.neg',[status(esa)],[t83_xboole_1])).

thf('6',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('11',plain,(
    ! [X33: $i,X34: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X33 @ X34 ) @ X34 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('12',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_B )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['8'])).

thf('14',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('16',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['9','14','15'])).

thf('17',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(simpl_trail,[status(thm)],['7','16'])).

thf(t78_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ A @ C ) ) ) )).

thf('18',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r1_xboole_0 @ X30 @ X31 )
      | ( ( k3_xboole_0 @ X30 @ ( k2_xboole_0 @ X31 @ X32 ) )
        = ( k3_xboole_0 @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t78_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','20'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('24',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('25',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['22','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','32'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('36',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['35','40'])).

thf('42',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('43',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['9','14'])).

thf('44',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['42','43'])).

thf('45',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['41','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Xy8sb1K6ke
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:31:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.76/0.95  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.76/0.95  % Solved by: fo/fo7.sh
% 0.76/0.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.95  % done 1216 iterations in 0.487s
% 0.76/0.95  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.76/0.95  % SZS output start Refutation
% 0.76/0.95  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.76/0.95  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.95  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.95  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.76/0.95  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.76/0.95  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.95  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.76/0.95  thf(t7_xboole_1, axiom,
% 0.76/0.95    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.76/0.95  thf('0', plain,
% 0.76/0.95      (![X35 : $i, X36 : $i]: (r1_tarski @ X35 @ (k2_xboole_0 @ X35 @ X36))),
% 0.76/0.95      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.76/0.95  thf(t43_xboole_1, axiom,
% 0.76/0.95    (![A:$i,B:$i,C:$i]:
% 0.76/0.95     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.76/0.95       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.76/0.95  thf('1', plain,
% 0.76/0.95      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.76/0.95         ((r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 0.76/0.95          | ~ (r1_tarski @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 0.76/0.95      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.76/0.95  thf('2', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 0.76/0.95      inference('sup-', [status(thm)], ['0', '1'])).
% 0.76/0.95  thf(t12_xboole_1, axiom,
% 0.76/0.95    (![A:$i,B:$i]:
% 0.76/0.95     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.76/0.95  thf('3', plain,
% 0.76/0.95      (![X7 : $i, X8 : $i]:
% 0.76/0.95         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.76/0.95      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.76/0.95  thf('4', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ X0) = (X0))),
% 0.76/0.95      inference('sup-', [status(thm)], ['2', '3'])).
% 0.76/0.95  thf(commutativity_k2_xboole_0, axiom,
% 0.76/0.95    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.76/0.95  thf('5', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.76/0.95      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.76/0.95  thf(t83_xboole_1, conjecture,
% 0.76/0.95    (![A:$i,B:$i]:
% 0.76/0.95     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.76/0.95  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.95    (~( ![A:$i,B:$i]:
% 0.76/0.95        ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ) )),
% 0.76/0.95    inference('cnf.neg', [status(esa)], [t83_xboole_1])).
% 0.76/0.95  thf('6', plain,
% 0.76/0.95      ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)) | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('7', plain,
% 0.76/0.95      (((r1_xboole_0 @ sk_A @ sk_B)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.76/0.95      inference('split', [status(esa)], ['6'])).
% 0.76/0.95  thf('8', plain,
% 0.76/0.95      ((((k4_xboole_0 @ sk_A @ sk_B) != (sk_A)) | ~ (r1_xboole_0 @ sk_A @ sk_B))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('9', plain,
% 0.76/0.95      (~ (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))) | 
% 0.76/0.95       ~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.76/0.95      inference('split', [status(esa)], ['8'])).
% 0.76/0.95  thf('10', plain,
% 0.76/0.95      ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))
% 0.76/0.95         <= ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))))),
% 0.76/0.95      inference('split', [status(esa)], ['6'])).
% 0.76/0.95  thf(t79_xboole_1, axiom,
% 0.76/0.95    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.76/0.95  thf('11', plain,
% 0.76/0.95      (![X33 : $i, X34 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X33 @ X34) @ X34)),
% 0.76/0.95      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.76/0.95  thf('12', plain,
% 0.76/0.95      (((r1_xboole_0 @ sk_A @ sk_B))
% 0.76/0.95         <= ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))))),
% 0.76/0.95      inference('sup+', [status(thm)], ['10', '11'])).
% 0.76/0.95  thf('13', plain,
% 0.76/0.95      ((~ (r1_xboole_0 @ sk_A @ sk_B)) <= (~ ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.76/0.95      inference('split', [status(esa)], ['8'])).
% 0.76/0.95  thf('14', plain,
% 0.76/0.95      (((r1_xboole_0 @ sk_A @ sk_B)) | 
% 0.76/0.95       ~ (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['12', '13'])).
% 0.76/0.95  thf('15', plain,
% 0.76/0.95      (((r1_xboole_0 @ sk_A @ sk_B)) | (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 0.76/0.95      inference('split', [status(esa)], ['6'])).
% 0.76/0.95  thf('16', plain, (((r1_xboole_0 @ sk_A @ sk_B))),
% 0.76/0.95      inference('sat_resolution*', [status(thm)], ['9', '14', '15'])).
% 0.76/0.95  thf('17', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.76/0.95      inference('simpl_trail', [status(thm)], ['7', '16'])).
% 0.76/0.95  thf(t78_xboole_1, axiom,
% 0.76/0.95    (![A:$i,B:$i,C:$i]:
% 0.76/0.95     ( ( r1_xboole_0 @ A @ B ) =>
% 0.76/0.95       ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.76/0.95         ( k3_xboole_0 @ A @ C ) ) ))).
% 0.76/0.95  thf('18', plain,
% 0.76/0.95      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.76/0.95         (~ (r1_xboole_0 @ X30 @ X31)
% 0.76/0.95          | ((k3_xboole_0 @ X30 @ (k2_xboole_0 @ X31 @ X32))
% 0.76/0.95              = (k3_xboole_0 @ X30 @ X32)))),
% 0.76/0.95      inference('cnf', [status(esa)], [t78_xboole_1])).
% 0.76/0.95  thf('19', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0))
% 0.76/0.95           = (k3_xboole_0 @ sk_A @ X0))),
% 0.76/0.95      inference('sup-', [status(thm)], ['17', '18'])).
% 0.76/0.95  thf('20', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_B))
% 0.76/0.95           = (k3_xboole_0 @ sk_A @ X0))),
% 0.76/0.95      inference('sup+', [status(thm)], ['5', '19'])).
% 0.76/0.95  thf('21', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((k3_xboole_0 @ sk_A @ sk_B)
% 0.76/0.95           = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ X0)))),
% 0.76/0.95      inference('sup+', [status(thm)], ['4', '20'])).
% 0.76/0.95  thf(commutativity_k3_xboole_0, axiom,
% 0.76/0.95    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.76/0.95  thf('22', plain,
% 0.76/0.95      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.76/0.95      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.76/0.95  thf(t48_xboole_1, axiom,
% 0.76/0.95    (![A:$i,B:$i]:
% 0.76/0.95     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.76/0.95  thf('23', plain,
% 0.76/0.95      (![X22 : $i, X23 : $i]:
% 0.76/0.95         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.76/0.95           = (k3_xboole_0 @ X22 @ X23))),
% 0.76/0.95      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.76/0.95  thf(t36_xboole_1, axiom,
% 0.76/0.95    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.76/0.95  thf('24', plain,
% 0.76/0.95      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 0.76/0.95      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.76/0.95  thf('25', plain,
% 0.76/0.95      (![X7 : $i, X8 : $i]:
% 0.76/0.95         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.76/0.95      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.76/0.95  thf('26', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.76/0.95      inference('sup-', [status(thm)], ['24', '25'])).
% 0.76/0.95  thf('27', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.76/0.95      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.76/0.95  thf('28', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.76/0.95      inference('demod', [status(thm)], ['26', '27'])).
% 0.76/0.95  thf('29', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 0.76/0.95      inference('sup+', [status(thm)], ['23', '28'])).
% 0.76/0.95  thf('30', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 0.76/0.95      inference('sup+', [status(thm)], ['22', '29'])).
% 0.76/0.95  thf('31', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ X0) = (X0))),
% 0.76/0.95      inference('sup-', [status(thm)], ['2', '3'])).
% 0.76/0.95  thf('32', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k4_xboole_0 @ X0 @ X0)
% 0.76/0.95           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.76/0.95      inference('sup+', [status(thm)], ['30', '31'])).
% 0.76/0.95  thf('33', plain,
% 0.76/0.95      (![X0 : $i]: ((k3_xboole_0 @ sk_A @ sk_B) = (k4_xboole_0 @ X0 @ X0))),
% 0.76/0.95      inference('demod', [status(thm)], ['21', '32'])).
% 0.76/0.95  thf(t47_xboole_1, axiom,
% 0.76/0.95    (![A:$i,B:$i]:
% 0.76/0.95     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.76/0.95  thf('34', plain,
% 0.76/0.95      (![X20 : $i, X21 : $i]:
% 0.76/0.95         ((k4_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21))
% 0.76/0.95           = (k4_xboole_0 @ X20 @ X21))),
% 0.76/0.95      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.76/0.95  thf('35', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ X0))
% 0.76/0.95           = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.76/0.95      inference('sup+', [status(thm)], ['33', '34'])).
% 0.76/0.95  thf(t39_xboole_1, axiom,
% 0.76/0.95    (![A:$i,B:$i]:
% 0.76/0.95     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.76/0.95  thf('36', plain,
% 0.76/0.95      (![X13 : $i, X14 : $i]:
% 0.76/0.95         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 0.76/0.95           = (k2_xboole_0 @ X13 @ X14))),
% 0.76/0.95      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.76/0.95  thf('37', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ X0) = (X0))),
% 0.76/0.95      inference('sup-', [status(thm)], ['2', '3'])).
% 0.76/0.95  thf('38', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ X0)
% 0.76/0.95           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X1)))),
% 0.76/0.95      inference('sup+', [status(thm)], ['36', '37'])).
% 0.76/0.95  thf('39', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ X0) = (X0))),
% 0.76/0.95      inference('sup-', [status(thm)], ['2', '3'])).
% 0.76/0.95  thf('40', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X1)))),
% 0.76/0.95      inference('demod', [status(thm)], ['38', '39'])).
% 0.76/0.95  thf('41', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.76/0.95      inference('demod', [status(thm)], ['35', '40'])).
% 0.76/0.95  thf('42', plain,
% 0.76/0.95      ((((k4_xboole_0 @ sk_A @ sk_B) != (sk_A)))
% 0.76/0.95         <= (~ (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))))),
% 0.76/0.95      inference('split', [status(esa)], ['8'])).
% 0.76/0.95  thf('43', plain, (~ (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 0.76/0.95      inference('sat_resolution*', [status(thm)], ['9', '14'])).
% 0.76/0.95  thf('44', plain, (((k4_xboole_0 @ sk_A @ sk_B) != (sk_A))),
% 0.76/0.95      inference('simpl_trail', [status(thm)], ['42', '43'])).
% 0.76/0.95  thf('45', plain, ($false),
% 0.76/0.95      inference('simplify_reflect-', [status(thm)], ['41', '44'])).
% 0.76/0.95  
% 0.76/0.95  % SZS output end Refutation
% 0.76/0.95  
% 0.76/0.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
