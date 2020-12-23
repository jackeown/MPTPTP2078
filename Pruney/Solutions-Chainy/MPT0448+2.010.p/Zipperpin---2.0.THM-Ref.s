%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.V82kaczmO9

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:01 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   43 (  50 expanded)
%              Number of leaves         :   16 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :  329 ( 392 expanded)
%              Number of equality atoms :   31 (  38 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

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
    ! [X2: $i] :
      ( ( k2_tarski @ X2 @ X2 )
      = ( k1_tarski @ X2 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X14
       != ( k2_tarski @ ( k4_tarski @ X10 @ X11 ) @ ( k4_tarski @ X12 @ X13 ) ) )
      | ( ( k1_relat_1 @ X14 )
        = ( k2_tarski @ X10 @ X12 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t24_relat_1])).

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X10 @ X11 ) @ ( k4_tarski @ X12 @ X13 ) ) )
      | ( ( k1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X10 @ X11 ) @ ( k4_tarski @ X12 @ X13 ) ) )
        = ( k2_tarski @ X10 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(fc7_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ C @ D ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X6 @ X7 ) @ ( k4_tarski @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[fc7_relat_1])).

thf('5',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X10 @ X11 ) @ ( k4_tarski @ X12 @ X13 ) ) )
      = ( k2_tarski @ X10 @ X12 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      = ( k2_tarski @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','5'])).

thf('7',plain,(
    ! [X2: $i] :
      ( ( k2_tarski @ X2 @ X2 )
      = ( k1_tarski @ X2 ) ) ),
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
    ! [X5: $i] :
      ( ( ( k3_relat_1 @ X5 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X5 ) @ ( k2_relat_1 @ X5 ) ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
        = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X2: $i] :
      ( ( k2_tarski @ X2 @ X2 )
      = ( k1_tarski @ X2 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('12',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X14
       != ( k2_tarski @ ( k4_tarski @ X10 @ X11 ) @ ( k4_tarski @ X12 @ X13 ) ) )
      | ( ( k2_relat_1 @ X14 )
        = ( k2_tarski @ X11 @ X13 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t24_relat_1])).

thf('13',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X10 @ X11 ) @ ( k4_tarski @ X12 @ X13 ) ) )
      | ( ( k2_relat_1 @ ( k2_tarski @ ( k4_tarski @ X10 @ X11 ) @ ( k4_tarski @ X12 @ X13 ) ) )
        = ( k2_tarski @ X11 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X6 @ X7 ) @ ( k4_tarski @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[fc7_relat_1])).

thf('15',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_relat_1 @ ( k2_tarski @ ( k4_tarski @ X10 @ X11 ) @ ( k4_tarski @ X12 @ X13 ) ) )
      = ( k2_tarski @ X11 @ X13 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X2: $i] :
      ( ( k2_tarski @ X2 @ X2 )
      = ( k1_tarski @ X2 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('20',plain,(
    ! [X2: $i] :
      ( ( k2_tarski @ X2 @ X2 )
      = ( k1_tarski @ X2 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('21',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X6 @ X7 ) @ ( k4_tarski @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[fc7_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['10','18','19','22'])).

thf('24',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','23'])).

thf('25',plain,(
    $false ),
    inference(simplify,[status(thm)],['24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.V82kaczmO9
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:54:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 15 iterations in 0.014s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.47  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.47  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.19/0.47  thf(t32_relat_1, conjecture,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =
% 0.19/0.47       ( k2_tarski @ A @ B ) ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (~( ![A:$i,B:$i]:
% 0.19/0.47        ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =
% 0.19/0.47          ( k2_tarski @ A @ B ) ) )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t32_relat_1])).
% 0.19/0.47  thf('0', plain,
% 0.19/0.47      (((k3_relat_1 @ (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))
% 0.19/0.47         != (k2_tarski @ sk_A @ sk_B))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(t69_enumset1, axiom,
% 0.19/0.47    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.47  thf('1', plain, (![X2 : $i]: ((k2_tarski @ X2 @ X2) = (k1_tarski @ X2))),
% 0.19/0.47      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.47  thf(t24_relat_1, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.19/0.47     ( ( v1_relat_1 @ E ) =>
% 0.19/0.47       ( ( ( E ) =
% 0.19/0.47           ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ C @ D ) ) ) =>
% 0.19/0.47         ( ( ( k1_relat_1 @ E ) = ( k2_tarski @ A @ C ) ) & 
% 0.19/0.47           ( ( k2_relat_1 @ E ) = ( k2_tarski @ B @ D ) ) ) ) ))).
% 0.19/0.47  thf('2', plain,
% 0.19/0.47      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.47         (((X14)
% 0.19/0.47            != (k2_tarski @ (k4_tarski @ X10 @ X11) @ (k4_tarski @ X12 @ X13)))
% 0.19/0.47          | ((k1_relat_1 @ X14) = (k2_tarski @ X10 @ X12))
% 0.19/0.47          | ~ (v1_relat_1 @ X14))),
% 0.19/0.47      inference('cnf', [status(esa)], [t24_relat_1])).
% 0.19/0.47  thf('3', plain,
% 0.19/0.47      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.47         (~ (v1_relat_1 @ 
% 0.19/0.47             (k2_tarski @ (k4_tarski @ X10 @ X11) @ (k4_tarski @ X12 @ X13)))
% 0.19/0.47          | ((k1_relat_1 @ 
% 0.19/0.47              (k2_tarski @ (k4_tarski @ X10 @ X11) @ (k4_tarski @ X12 @ X13)))
% 0.19/0.47              = (k2_tarski @ X10 @ X12)))),
% 0.19/0.47      inference('simplify', [status(thm)], ['2'])).
% 0.19/0.47  thf(fc7_relat_1, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.47     ( v1_relat_1 @
% 0.19/0.47       ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ C @ D ) ) ))).
% 0.19/0.47  thf('4', plain,
% 0.19/0.47      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.47         (v1_relat_1 @ 
% 0.19/0.47          (k2_tarski @ (k4_tarski @ X6 @ X7) @ (k4_tarski @ X8 @ X9)))),
% 0.19/0.47      inference('cnf', [status(esa)], [fc7_relat_1])).
% 0.19/0.47  thf('5', plain,
% 0.19/0.47      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.47         ((k1_relat_1 @ 
% 0.19/0.47           (k2_tarski @ (k4_tarski @ X10 @ X11) @ (k4_tarski @ X12 @ X13)))
% 0.19/0.47           = (k2_tarski @ X10 @ X12))),
% 0.19/0.47      inference('demod', [status(thm)], ['3', '4'])).
% 0.19/0.47  thf('6', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.19/0.47           = (k2_tarski @ X1 @ X1))),
% 0.19/0.47      inference('sup+', [status(thm)], ['1', '5'])).
% 0.19/0.47  thf('7', plain, (![X2 : $i]: ((k2_tarski @ X2 @ X2) = (k1_tarski @ X2))),
% 0.19/0.47      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.47  thf('8', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) = (k1_tarski @ X1))),
% 0.19/0.47      inference('demod', [status(thm)], ['6', '7'])).
% 0.19/0.47  thf(d6_relat_1, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( v1_relat_1 @ A ) =>
% 0.19/0.47       ( ( k3_relat_1 @ A ) =
% 0.19/0.47         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.19/0.47  thf('9', plain,
% 0.19/0.47      (![X5 : $i]:
% 0.19/0.47         (((k3_relat_1 @ X5)
% 0.19/0.47            = (k2_xboole_0 @ (k1_relat_1 @ X5) @ (k2_relat_1 @ X5)))
% 0.19/0.47          | ~ (v1_relat_1 @ X5))),
% 0.19/0.47      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.19/0.47  thf('10', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         (((k3_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 0.19/0.47            = (k2_xboole_0 @ (k1_tarski @ X0) @ 
% 0.19/0.47               (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))))
% 0.19/0.47          | ~ (v1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))))),
% 0.19/0.47      inference('sup+', [status(thm)], ['8', '9'])).
% 0.19/0.47  thf('11', plain, (![X2 : $i]: ((k2_tarski @ X2 @ X2) = (k1_tarski @ X2))),
% 0.19/0.47      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.47  thf('12', plain,
% 0.19/0.47      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.47         (((X14)
% 0.19/0.47            != (k2_tarski @ (k4_tarski @ X10 @ X11) @ (k4_tarski @ X12 @ X13)))
% 0.19/0.47          | ((k2_relat_1 @ X14) = (k2_tarski @ X11 @ X13))
% 0.19/0.47          | ~ (v1_relat_1 @ X14))),
% 0.19/0.47      inference('cnf', [status(esa)], [t24_relat_1])).
% 0.19/0.47  thf('13', plain,
% 0.19/0.47      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.47         (~ (v1_relat_1 @ 
% 0.19/0.47             (k2_tarski @ (k4_tarski @ X10 @ X11) @ (k4_tarski @ X12 @ X13)))
% 0.19/0.47          | ((k2_relat_1 @ 
% 0.19/0.47              (k2_tarski @ (k4_tarski @ X10 @ X11) @ (k4_tarski @ X12 @ X13)))
% 0.19/0.47              = (k2_tarski @ X11 @ X13)))),
% 0.19/0.47      inference('simplify', [status(thm)], ['12'])).
% 0.19/0.47  thf('14', plain,
% 0.19/0.47      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.47         (v1_relat_1 @ 
% 0.19/0.47          (k2_tarski @ (k4_tarski @ X6 @ X7) @ (k4_tarski @ X8 @ X9)))),
% 0.19/0.47      inference('cnf', [status(esa)], [fc7_relat_1])).
% 0.19/0.47  thf('15', plain,
% 0.19/0.47      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.47         ((k2_relat_1 @ 
% 0.19/0.47           (k2_tarski @ (k4_tarski @ X10 @ X11) @ (k4_tarski @ X12 @ X13)))
% 0.19/0.47           = (k2_tarski @ X11 @ X13))),
% 0.19/0.47      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.47  thf('16', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         ((k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.19/0.47           = (k2_tarski @ X0 @ X0))),
% 0.19/0.47      inference('sup+', [status(thm)], ['11', '15'])).
% 0.19/0.47  thf('17', plain, (![X2 : $i]: ((k2_tarski @ X2 @ X2) = (k1_tarski @ X2))),
% 0.19/0.47      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.47  thf('18', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         ((k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) = (k1_tarski @ X0))),
% 0.19/0.47      inference('demod', [status(thm)], ['16', '17'])).
% 0.19/0.47  thf(t41_enumset1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( k2_tarski @ A @ B ) =
% 0.19/0.47       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.19/0.47  thf('19', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         ((k2_tarski @ X0 @ X1)
% 0.19/0.47           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.19/0.47      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.19/0.47  thf('20', plain, (![X2 : $i]: ((k2_tarski @ X2 @ X2) = (k1_tarski @ X2))),
% 0.19/0.47      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.47  thf('21', plain,
% 0.19/0.47      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.47         (v1_relat_1 @ 
% 0.19/0.47          (k2_tarski @ (k4_tarski @ X6 @ X7) @ (k4_tarski @ X8 @ X9)))),
% 0.19/0.47      inference('cnf', [status(esa)], [fc7_relat_1])).
% 0.19/0.47  thf('22', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.19/0.47      inference('sup+', [status(thm)], ['20', '21'])).
% 0.19/0.47  thf('23', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         ((k3_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 0.19/0.47           = (k2_tarski @ X0 @ X1))),
% 0.19/0.47      inference('demod', [status(thm)], ['10', '18', '19', '22'])).
% 0.19/0.47  thf('24', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.19/0.47      inference('demod', [status(thm)], ['0', '23'])).
% 0.19/0.47  thf('25', plain, ($false), inference('simplify', [status(thm)], ['24'])).
% 0.19/0.47  
% 0.19/0.47  % SZS output end Refutation
% 0.19/0.47  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
