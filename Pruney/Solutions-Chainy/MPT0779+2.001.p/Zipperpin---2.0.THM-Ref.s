%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PZbzCNTyXa

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:24 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   42 (  64 expanded)
%              Number of leaves         :   15 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :  247 ( 405 expanded)
%              Number of equality atoms :   32 (  54 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(t26_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
        = ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X8 @ X9 ) @ X10 )
        = ( k2_wellord1 @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t26_wellord1])).

thf(t28_wellord1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ B @ A ) @ A )
        = ( k2_wellord1 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( k2_wellord1 @ ( k2_wellord1 @ B @ A ) @ A )
          = ( k2_wellord1 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_wellord1])).

thf('1',plain,(
    ( k2_wellord1 @ ( k2_wellord1 @ sk_B @ sk_A ) @ sk_A )
 != ( k2_wellord1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k2_wellord1 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_A ) )
     != ( k2_wellord1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ( k2_wellord1 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_A ) )
 != ( k2_wellord1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X6 @ X7 ) @ ( k4_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

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
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ ( k3_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['11','14'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('23',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ( k2_wellord1 @ sk_B @ sk_A )
 != ( k2_wellord1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['4','23'])).

thf('25',plain,(
    $false ),
    inference(simplify,[status(thm)],['24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PZbzCNTyXa
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:57:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.47  % Solved by: fo/fo7.sh
% 0.22/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.47  % done 20 iterations in 0.012s
% 0.22/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.47  % SZS output start Refutation
% 0.22/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.47  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.22/0.47  thf(t26_wellord1, axiom,
% 0.22/0.47    (![A:$i,B:$i,C:$i]:
% 0.22/0.47     ( ( v1_relat_1 @ C ) =>
% 0.22/0.47       ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 0.22/0.47         ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.22/0.47  thf('0', plain,
% 0.22/0.47      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.47         (((k2_wellord1 @ (k2_wellord1 @ X8 @ X9) @ X10)
% 0.22/0.47            = (k2_wellord1 @ X8 @ (k3_xboole_0 @ X9 @ X10)))
% 0.22/0.47          | ~ (v1_relat_1 @ X8))),
% 0.22/0.47      inference('cnf', [status(esa)], [t26_wellord1])).
% 0.22/0.47  thf(t28_wellord1, conjecture,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( v1_relat_1 @ B ) =>
% 0.22/0.47       ( ( k2_wellord1 @ ( k2_wellord1 @ B @ A ) @ A ) =
% 0.22/0.47         ( k2_wellord1 @ B @ A ) ) ))).
% 0.22/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.47    (~( ![A:$i,B:$i]:
% 0.22/0.47        ( ( v1_relat_1 @ B ) =>
% 0.22/0.47          ( ( k2_wellord1 @ ( k2_wellord1 @ B @ A ) @ A ) =
% 0.22/0.47            ( k2_wellord1 @ B @ A ) ) ) )),
% 0.22/0.47    inference('cnf.neg', [status(esa)], [t28_wellord1])).
% 0.22/0.47  thf('1', plain,
% 0.22/0.47      (((k2_wellord1 @ (k2_wellord1 @ sk_B @ sk_A) @ sk_A)
% 0.22/0.47         != (k2_wellord1 @ sk_B @ sk_A))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('2', plain,
% 0.22/0.47      ((((k2_wellord1 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_A))
% 0.22/0.47          != (k2_wellord1 @ sk_B @ sk_A))
% 0.22/0.47        | ~ (v1_relat_1 @ sk_B))),
% 0.22/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.47  thf('3', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('4', plain,
% 0.22/0.47      (((k2_wellord1 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_A))
% 0.22/0.47         != (k2_wellord1 @ sk_B @ sk_A))),
% 0.22/0.47      inference('demod', [status(thm)], ['2', '3'])).
% 0.22/0.47  thf(t2_boole, axiom,
% 0.22/0.47    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.47  thf('5', plain,
% 0.22/0.47      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.47      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.47  thf(t51_xboole_1, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.22/0.47       ( A ) ))).
% 0.22/0.47  thf('6', plain,
% 0.22/0.47      (![X6 : $i, X7 : $i]:
% 0.22/0.47         ((k2_xboole_0 @ (k3_xboole_0 @ X6 @ X7) @ (k4_xboole_0 @ X6 @ X7))
% 0.22/0.47           = (X6))),
% 0.22/0.47      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.22/0.47  thf(commutativity_k2_xboole_0, axiom,
% 0.22/0.47    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.22/0.47  thf('7', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.22/0.47  thf('8', plain,
% 0.22/0.47      (![X6 : $i, X7 : $i]:
% 0.22/0.47         ((k2_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ (k3_xboole_0 @ X6 @ X7))
% 0.22/0.47           = (X6))),
% 0.22/0.47      inference('demod', [status(thm)], ['6', '7'])).
% 0.22/0.47  thf('9', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0) = (X0))),
% 0.22/0.47      inference('sup+', [status(thm)], ['5', '8'])).
% 0.22/0.47  thf('10', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.22/0.47  thf('11', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         ((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 0.22/0.47      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.47  thf('12', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.22/0.47  thf(t1_boole, axiom,
% 0.22/0.47    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.47  thf('13', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.22/0.47      inference('cnf', [status(esa)], [t1_boole])).
% 0.22/0.47  thf('14', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.22/0.47      inference('sup+', [status(thm)], ['12', '13'])).
% 0.22/0.47  thf('15', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.22/0.47      inference('demod', [status(thm)], ['11', '14'])).
% 0.22/0.47  thf(t48_xboole_1, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.47  thf('16', plain,
% 0.22/0.47      (![X4 : $i, X5 : $i]:
% 0.22/0.47         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X4 @ X5))
% 0.22/0.47           = (k3_xboole_0 @ X4 @ X5))),
% 0.22/0.47      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.47  thf('17', plain,
% 0.22/0.47      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.47      inference('sup+', [status(thm)], ['15', '16'])).
% 0.22/0.47  thf('18', plain,
% 0.22/0.47      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.47      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.47  thf('19', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.47      inference('demod', [status(thm)], ['17', '18'])).
% 0.22/0.47  thf('20', plain,
% 0.22/0.47      (![X4 : $i, X5 : $i]:
% 0.22/0.47         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X4 @ X5))
% 0.22/0.47           = (k3_xboole_0 @ X4 @ X5))),
% 0.22/0.47      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.47  thf('21', plain,
% 0.22/0.47      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.22/0.47      inference('sup+', [status(thm)], ['19', '20'])).
% 0.22/0.47  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.22/0.47      inference('demod', [status(thm)], ['11', '14'])).
% 0.22/0.47  thf('23', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.22/0.47      inference('demod', [status(thm)], ['21', '22'])).
% 0.22/0.47  thf('24', plain,
% 0.22/0.47      (((k2_wellord1 @ sk_B @ sk_A) != (k2_wellord1 @ sk_B @ sk_A))),
% 0.22/0.47      inference('demod', [status(thm)], ['4', '23'])).
% 0.22/0.47  thf('25', plain, ($false), inference('simplify', [status(thm)], ['24'])).
% 0.22/0.47  
% 0.22/0.47  % SZS output end Refutation
% 0.22/0.47  
% 0.22/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
