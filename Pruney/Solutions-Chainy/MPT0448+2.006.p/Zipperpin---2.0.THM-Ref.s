%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4tKslqJJP5

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 (  58 expanded)
%              Number of leaves         :   18 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :  385 ( 454 expanded)
%              Number of equality atoms :   37 (  45 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t32_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ A @ B ) ) )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ A @ B ) ) )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t32_relat_1])).

thf('0',plain,(
    ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t24_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( v1_relat_1 @ E )
     => ( ( E
          = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ C @ D ) ) )
       => ( ( ( k1_relat_1 @ E )
            = ( k2_tarski @ A @ C ) )
          & ( ( k2_relat_1 @ E )
            = ( k2_tarski @ B @ D ) ) ) ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( X26
       != ( k2_tarski @ ( k4_tarski @ X22 @ X23 ) @ ( k4_tarski @ X24 @ X25 ) ) )
      | ( ( k1_relat_1 @ X26 )
        = ( k2_tarski @ X22 @ X24 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t24_relat_1])).

thf('3',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X22 @ X23 ) @ ( k4_tarski @ X24 @ X25 ) ) )
      | ( ( k1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X22 @ X23 ) @ ( k4_tarski @ X24 @ X25 ) ) )
        = ( k2_tarski @ X22 @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(fc7_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ C @ D ) ) ) )).

thf('4',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X18 @ X19 ) @ ( k4_tarski @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[fc7_relat_1])).

thf('5',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( k1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X22 @ X23 ) @ ( k4_tarski @ X24 @ X25 ) ) )
      = ( k2_tarski @ X22 @ X24 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      = ( k2_tarski @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','5'])).

thf('7',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      = ( k1_tarski @ X1 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('9',plain,(
    ! [X17: $i] :
      ( ( ( k3_relat_1 @ X17 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X17 ) @ ( k2_relat_1 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
        = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('12',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( X26
       != ( k2_tarski @ ( k4_tarski @ X22 @ X23 ) @ ( k4_tarski @ X24 @ X25 ) ) )
      | ( ( k2_relat_1 @ X26 )
        = ( k2_tarski @ X23 @ X25 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t24_relat_1])).

thf('13',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X22 @ X23 ) @ ( k4_tarski @ X24 @ X25 ) ) )
      | ( ( k2_relat_1 @ ( k2_tarski @ ( k4_tarski @ X22 @ X23 ) @ ( k4_tarski @ X24 @ X25 ) ) )
        = ( k2_tarski @ X23 @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X18 @ X19 ) @ ( k4_tarski @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[fc7_relat_1])).

thf('15',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( k2_relat_1 @ ( k2_tarski @ ( k4_tarski @ X22 @ X23 ) @ ( k4_tarski @ X24 @ X25 ) ) )
      = ( k2_tarski @ X23 @ X25 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('20',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X18 @ X19 ) @ ( k4_tarski @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[fc7_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['10','18','21'])).

thf('23',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t43_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ) )).

thf('24',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k1_enumset1 @ X2 @ X3 @ X4 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X3 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k1_enumset1 @ X6 @ X6 @ X7 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['22','27'])).

thf('29',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','28'])).

thf('30',plain,(
    $false ),
    inference(simplify,[status(thm)],['29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4tKslqJJP5
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:05:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 46 iterations in 0.027s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.48  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.48  thf(t32_relat_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =
% 0.21/0.48       ( k2_tarski @ A @ B ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i]:
% 0.21/0.48        ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =
% 0.21/0.48          ( k2_tarski @ A @ B ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t32_relat_1])).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      (((k3_relat_1 @ (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))
% 0.21/0.48         != (k2_tarski @ sk_A @ sk_B))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t69_enumset1, axiom,
% 0.21/0.48    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.48  thf('1', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.48  thf(t24_relat_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ E ) =>
% 0.21/0.48       ( ( ( E ) =
% 0.21/0.48           ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ C @ D ) ) ) =>
% 0.21/0.48         ( ( ( k1_relat_1 @ E ) = ( k2_tarski @ A @ C ) ) & 
% 0.21/0.48           ( ( k2_relat_1 @ E ) = ( k2_tarski @ B @ D ) ) ) ) ))).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.48         (((X26)
% 0.21/0.48            != (k2_tarski @ (k4_tarski @ X22 @ X23) @ (k4_tarski @ X24 @ X25)))
% 0.21/0.48          | ((k1_relat_1 @ X26) = (k2_tarski @ X22 @ X24))
% 0.21/0.48          | ~ (v1_relat_1 @ X26))),
% 0.21/0.48      inference('cnf', [status(esa)], [t24_relat_1])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ 
% 0.21/0.48             (k2_tarski @ (k4_tarski @ X22 @ X23) @ (k4_tarski @ X24 @ X25)))
% 0.21/0.48          | ((k1_relat_1 @ 
% 0.21/0.48              (k2_tarski @ (k4_tarski @ X22 @ X23) @ (k4_tarski @ X24 @ X25)))
% 0.21/0.48              = (k2_tarski @ X22 @ X24)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.48  thf(fc7_relat_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48     ( v1_relat_1 @
% 0.21/0.48       ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ C @ D ) ) ))).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.48         (v1_relat_1 @ 
% 0.21/0.48          (k2_tarski @ (k4_tarski @ X18 @ X19) @ (k4_tarski @ X20 @ X21)))),
% 0.21/0.48      inference('cnf', [status(esa)], [fc7_relat_1])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.48         ((k1_relat_1 @ 
% 0.21/0.48           (k2_tarski @ (k4_tarski @ X22 @ X23) @ (k4_tarski @ X24 @ X25)))
% 0.21/0.48           = (k2_tarski @ X22 @ X24))),
% 0.21/0.48      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.21/0.48           = (k2_tarski @ X1 @ X1))),
% 0.21/0.48      inference('sup+', [status(thm)], ['1', '5'])).
% 0.21/0.48  thf('7', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) = (k1_tarski @ X1))),
% 0.21/0.48      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.48  thf(d6_relat_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) =>
% 0.21/0.48       ( ( k3_relat_1 @ A ) =
% 0.21/0.48         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X17 : $i]:
% 0.21/0.48         (((k3_relat_1 @ X17)
% 0.21/0.48            = (k2_xboole_0 @ (k1_relat_1 @ X17) @ (k2_relat_1 @ X17)))
% 0.21/0.48          | ~ (v1_relat_1 @ X17))),
% 0.21/0.48      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (((k3_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 0.21/0.48            = (k2_xboole_0 @ (k1_tarski @ X0) @ 
% 0.21/0.48               (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))))
% 0.21/0.48          | ~ (v1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))))),
% 0.21/0.48      inference('sup+', [status(thm)], ['8', '9'])).
% 0.21/0.48  thf('11', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.48         (((X26)
% 0.21/0.48            != (k2_tarski @ (k4_tarski @ X22 @ X23) @ (k4_tarski @ X24 @ X25)))
% 0.21/0.48          | ((k2_relat_1 @ X26) = (k2_tarski @ X23 @ X25))
% 0.21/0.48          | ~ (v1_relat_1 @ X26))),
% 0.21/0.48      inference('cnf', [status(esa)], [t24_relat_1])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ 
% 0.21/0.48             (k2_tarski @ (k4_tarski @ X22 @ X23) @ (k4_tarski @ X24 @ X25)))
% 0.21/0.48          | ((k2_relat_1 @ 
% 0.21/0.48              (k2_tarski @ (k4_tarski @ X22 @ X23) @ (k4_tarski @ X24 @ X25)))
% 0.21/0.48              = (k2_tarski @ X23 @ X25)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.48         (v1_relat_1 @ 
% 0.21/0.48          (k2_tarski @ (k4_tarski @ X18 @ X19) @ (k4_tarski @ X20 @ X21)))),
% 0.21/0.48      inference('cnf', [status(esa)], [fc7_relat_1])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.48         ((k2_relat_1 @ 
% 0.21/0.48           (k2_tarski @ (k4_tarski @ X22 @ X23) @ (k4_tarski @ X24 @ X25)))
% 0.21/0.48           = (k2_tarski @ X23 @ X25))),
% 0.21/0.48      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.21/0.48           = (k2_tarski @ X0 @ X0))),
% 0.21/0.48      inference('sup+', [status(thm)], ['11', '15'])).
% 0.21/0.48  thf('17', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) = (k1_tarski @ X0))),
% 0.21/0.48      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.48  thf('19', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.48         (v1_relat_1 @ 
% 0.21/0.48          (k2_tarski @ (k4_tarski @ X18 @ X19) @ (k4_tarski @ X20 @ X21)))),
% 0.21/0.48      inference('cnf', [status(esa)], [fc7_relat_1])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.21/0.48      inference('sup+', [status(thm)], ['19', '20'])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((k3_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 0.21/0.48           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.21/0.48      inference('demod', [status(thm)], ['10', '18', '21'])).
% 0.21/0.48  thf('23', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.48  thf(t43_enumset1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.21/0.48       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ))).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.48         ((k1_enumset1 @ X2 @ X3 @ X4)
% 0.21/0.48           = (k2_xboole_0 @ (k2_tarski @ X2 @ X3) @ (k1_tarski @ X4)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((k1_enumset1 @ X0 @ X0 @ X1)
% 0.21/0.48           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.21/0.48      inference('sup+', [status(thm)], ['23', '24'])).
% 0.21/0.48  thf(t70_enumset1, axiom,
% 0.21/0.48    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i]:
% 0.21/0.48         ((k1_enumset1 @ X6 @ X6 @ X7) = (k2_tarski @ X6 @ X7))),
% 0.21/0.48      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.21/0.48           = (k2_tarski @ X1 @ X0))),
% 0.21/0.48      inference('sup+', [status(thm)], ['25', '26'])).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((k3_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 0.21/0.48           = (k2_tarski @ X0 @ X1))),
% 0.21/0.48      inference('demod', [status(thm)], ['22', '27'])).
% 0.21/0.48  thf('29', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['0', '28'])).
% 0.21/0.48  thf('30', plain, ($false), inference('simplify', [status(thm)], ['29'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
