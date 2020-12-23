%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Dydq1rTCSU

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:22 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   47 (  90 expanded)
%              Number of leaves         :   14 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :  359 ( 731 expanded)
%              Number of equality atoms :   39 (  82 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(t70_enumset1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_enumset1 @ A @ A @ B )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t70_enumset1])).

thf('0',plain,(
    ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('1',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_tarski @ X29 @ X30 )
      = ( k2_xboole_0 @ ( k1_tarski @ X29 ) @ ( k1_tarski @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_tarski @ X29 @ X30 )
      = ( k2_xboole_0 @ ( k1_tarski @ X29 ) @ ( k1_tarski @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
 != ( k2_tarski @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['0','5'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('7',plain,(
    ! [X38: $i] :
      ( ( k2_tarski @ X38 @ X38 )
      = ( k1_tarski @ X38 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k1_enumset1 @ X31 @ X32 @ X33 )
      = ( k2_xboole_0 @ ( k1_tarski @ X31 ) @ ( k2_tarski @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_tarski @ X29 @ X30 )
      = ( k2_xboole_0 @ ( k1_tarski @ X29 ) @ ( k1_tarski @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k1_enumset1 @ X31 @ X32 @ X33 )
      = ( k2_xboole_0 @ ( k1_tarski @ X31 ) @ ( k2_tarski @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k1_enumset1 @ X1 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('14',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k2_enumset1 @ X34 @ X35 @ X36 @ X37 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X34 @ X35 @ X36 ) @ ( k1_tarski @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_enumset1 @ X3 @ X2 @ X1 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X1 @ X0 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X38: $i] :
      ( ( k2_tarski @ X38 @ X38 )
      = ( k1_tarski @ X38 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('19',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k2_enumset1 @ X25 @ X26 @ X27 @ X28 )
      = ( k2_xboole_0 @ ( k2_tarski @ X25 @ X26 ) @ ( k2_tarski @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k1_enumset1 @ X31 @ X32 @ X33 )
      = ( k2_xboole_0 @ ( k1_tarski @ X31 ) @ ( k2_tarski @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X1 )
      = ( k1_enumset1 @ X1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('30',plain,(
    ( k2_tarski @ sk_B @ sk_A )
 != ( k2_tarski @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['6','23','28','29'])).

thf('31',plain,(
    $false ),
    inference(simplify,[status(thm)],['30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Dydq1rTCSU
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:44:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.59/0.79  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.79  % Solved by: fo/fo7.sh
% 0.59/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.79  % done 975 iterations in 0.339s
% 0.59/0.79  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.79  % SZS output start Refutation
% 0.59/0.79  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.79  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.59/0.79  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.59/0.79  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.59/0.79  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.59/0.79  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.59/0.79  thf(t70_enumset1, conjecture,
% 0.59/0.79    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.59/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.79    (~( ![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ) )),
% 0.59/0.79    inference('cnf.neg', [status(esa)], [t70_enumset1])).
% 0.59/0.79  thf('0', plain,
% 0.59/0.79      (((k1_enumset1 @ sk_A @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf(t41_enumset1, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( k2_tarski @ A @ B ) =
% 0.59/0.79       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.59/0.79  thf('1', plain,
% 0.59/0.79      (![X29 : $i, X30 : $i]:
% 0.59/0.79         ((k2_tarski @ X29 @ X30)
% 0.59/0.79           = (k2_xboole_0 @ (k1_tarski @ X29) @ (k1_tarski @ X30)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.59/0.79  thf(commutativity_k2_xboole_0, axiom,
% 0.59/0.79    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.59/0.79  thf('2', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.79      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.59/0.79  thf('3', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.59/0.79           = (k2_tarski @ X1 @ X0))),
% 0.59/0.79      inference('sup+', [status(thm)], ['1', '2'])).
% 0.59/0.79  thf('4', plain,
% 0.59/0.79      (![X29 : $i, X30 : $i]:
% 0.59/0.79         ((k2_tarski @ X29 @ X30)
% 0.59/0.79           = (k2_xboole_0 @ (k1_tarski @ X29) @ (k1_tarski @ X30)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.59/0.79  thf('5', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]: ((k2_tarski @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 0.59/0.79      inference('sup+', [status(thm)], ['3', '4'])).
% 0.59/0.79  thf('6', plain,
% 0.59/0.79      (((k1_enumset1 @ sk_A @ sk_A @ sk_B) != (k2_tarski @ sk_B @ sk_A))),
% 0.59/0.79      inference('demod', [status(thm)], ['0', '5'])).
% 0.59/0.79  thf(t69_enumset1, axiom,
% 0.59/0.79    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.59/0.79  thf('7', plain, (![X38 : $i]: ((k2_tarski @ X38 @ X38) = (k1_tarski @ X38))),
% 0.59/0.79      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.59/0.79  thf(t42_enumset1, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i]:
% 0.59/0.79     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.59/0.79       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.59/0.79  thf('8', plain,
% 0.59/0.79      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.59/0.79         ((k1_enumset1 @ X31 @ X32 @ X33)
% 0.59/0.79           = (k2_xboole_0 @ (k1_tarski @ X31) @ (k2_tarski @ X32 @ X33)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.59/0.79  thf('9', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         ((k1_enumset1 @ X1 @ X0 @ X0)
% 0.59/0.79           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.59/0.79      inference('sup+', [status(thm)], ['7', '8'])).
% 0.59/0.79  thf('10', plain,
% 0.59/0.79      (![X29 : $i, X30 : $i]:
% 0.59/0.79         ((k2_tarski @ X29 @ X30)
% 0.59/0.79           = (k2_xboole_0 @ (k1_tarski @ X29) @ (k1_tarski @ X30)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.59/0.79  thf('11', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.59/0.79      inference('demod', [status(thm)], ['9', '10'])).
% 0.59/0.79  thf('12', plain,
% 0.59/0.79      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.59/0.79         ((k1_enumset1 @ X31 @ X32 @ X33)
% 0.59/0.79           = (k2_xboole_0 @ (k1_tarski @ X31) @ (k2_tarski @ X32 @ X33)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.59/0.79  thf('13', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.79         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.59/0.79           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k1_enumset1 @ X1 @ X0 @ X0)))),
% 0.59/0.79      inference('sup+', [status(thm)], ['11', '12'])).
% 0.59/0.79  thf(t46_enumset1, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.79     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.59/0.79       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.59/0.79  thf('14', plain,
% 0.59/0.79      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.59/0.79         ((k2_enumset1 @ X34 @ X35 @ X36 @ X37)
% 0.59/0.79           = (k2_xboole_0 @ (k1_enumset1 @ X34 @ X35 @ X36) @ (k1_tarski @ X37)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.59/0.79  thf('15', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.79      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.59/0.79  thf('16', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.79         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_enumset1 @ X3 @ X2 @ X1))
% 0.59/0.79           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.59/0.79      inference('sup+', [status(thm)], ['14', '15'])).
% 0.59/0.79  thf('17', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.79         ((k1_enumset1 @ X2 @ X1 @ X0) = (k2_enumset1 @ X1 @ X0 @ X0 @ X2))),
% 0.59/0.79      inference('demod', [status(thm)], ['13', '16'])).
% 0.59/0.79  thf('18', plain,
% 0.59/0.79      (![X38 : $i]: ((k2_tarski @ X38 @ X38) = (k1_tarski @ X38))),
% 0.59/0.79      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.59/0.79  thf(l53_enumset1, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.79     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.59/0.79       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.59/0.79  thf('19', plain,
% 0.59/0.79      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.59/0.79         ((k2_enumset1 @ X25 @ X26 @ X27 @ X28)
% 0.59/0.79           = (k2_xboole_0 @ (k2_tarski @ X25 @ X26) @ (k2_tarski @ X27 @ X28)))),
% 0.59/0.79      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.59/0.79  thf('20', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.79         ((k2_enumset1 @ X0 @ X0 @ X2 @ X1)
% 0.59/0.79           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 0.59/0.79      inference('sup+', [status(thm)], ['18', '19'])).
% 0.59/0.79  thf('21', plain,
% 0.59/0.79      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.59/0.79         ((k1_enumset1 @ X31 @ X32 @ X33)
% 0.59/0.79           = (k2_xboole_0 @ (k1_tarski @ X31) @ (k2_tarski @ X32 @ X33)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.59/0.79  thf('22', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.79         ((k2_enumset1 @ X0 @ X0 @ X2 @ X1) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 0.59/0.79      inference('demod', [status(thm)], ['20', '21'])).
% 0.59/0.79  thf('23', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         ((k1_enumset1 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X0 @ X1))),
% 0.59/0.79      inference('sup+', [status(thm)], ['17', '22'])).
% 0.59/0.79  thf('24', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]: ((k2_tarski @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 0.59/0.79      inference('sup+', [status(thm)], ['3', '4'])).
% 0.59/0.79  thf('25', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.59/0.79      inference('demod', [status(thm)], ['9', '10'])).
% 0.59/0.79  thf('26', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         ((k1_enumset1 @ X0 @ X1 @ X1) = (k2_tarski @ X1 @ X0))),
% 0.59/0.79      inference('sup+', [status(thm)], ['24', '25'])).
% 0.59/0.79  thf('27', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.59/0.79      inference('demod', [status(thm)], ['9', '10'])).
% 0.59/0.79  thf('28', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         ((k1_enumset1 @ X0 @ X1 @ X1) = (k1_enumset1 @ X1 @ X0 @ X0))),
% 0.59/0.79      inference('sup+', [status(thm)], ['26', '27'])).
% 0.59/0.79  thf('29', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         ((k1_enumset1 @ X0 @ X1 @ X1) = (k2_tarski @ X1 @ X0))),
% 0.59/0.79      inference('sup+', [status(thm)], ['24', '25'])).
% 0.59/0.79  thf('30', plain, (((k2_tarski @ sk_B @ sk_A) != (k2_tarski @ sk_B @ sk_A))),
% 0.59/0.79      inference('demod', [status(thm)], ['6', '23', '28', '29'])).
% 0.59/0.79  thf('31', plain, ($false), inference('simplify', [status(thm)], ['30'])).
% 0.59/0.79  
% 0.59/0.79  % SZS output end Refutation
% 0.59/0.79  
% 0.59/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
