%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7ARfBq1wGd

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:24 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   51 (  70 expanded)
%              Number of leaves         :   20 (  31 expanded)
%              Depth                    :   12
%              Number of atoms          :  373 ( 563 expanded)
%              Number of equality atoms :   50 (  73 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('0',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X7 ) @ ( k2_tarski @ X8 @ X9 ) )
      = ( k2_tarski @ ( k4_tarski @ X7 @ X8 ) @ ( k4_tarski @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t195_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = A )
            & ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = B ) ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) )
        = X11 )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
        = ( k1_tarski @ X1 ) )
      | ( ( k2_tarski @ X0 @ X0 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(fc3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc3_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('7',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
        = ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('9',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_mcart_1 @ X13 @ X14 @ X15 )
      = ( k4_tarski @ ( k4_tarski @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
        = ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) ) )
        = ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) )
      | ( ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t97_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_relat_1 @ ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) )
      = ( k1_tarski @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k1_relat_1 @ ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) )
        = ( k1_tarski @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t97_mcart_1])).

thf('12',plain,(
    ( k1_relat_1 @ ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) ) ) )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) )
     != ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,
    ( ( ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('17',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X7 ) @ ( k2_tarski @ X8 @ X9 ) )
      = ( k2_tarski @ ( k4_tarski @ X7 @ X8 ) @ ( k4_tarski @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ ( k4_tarski @ X1 @ X0 ) @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t130_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != k1_xboole_0 )
     => ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A )
         != k1_xboole_0 )
        & ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) )
         != k1_xboole_0 ) ) ) )).

thf('21',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X5 @ ( k1_tarski @ X6 ) )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t130_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['15','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('25',plain,(
    ! [X3: $i,X4: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc3_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['27','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7ARfBq1wGd
% 0.15/0.38  % Computer   : n007.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 12:40:06 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.24/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.57  % Solved by: fo/fo7.sh
% 0.24/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.57  % done 247 iterations in 0.115s
% 0.24/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.57  % SZS output start Refutation
% 0.24/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.24/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.24/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.24/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.24/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.24/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.24/0.57  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.24/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.24/0.57  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.24/0.57  thf(t36_zfmisc_1, axiom,
% 0.24/0.57    (![A:$i,B:$i,C:$i]:
% 0.24/0.57     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 0.24/0.57         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 0.24/0.57       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 0.24/0.57         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 0.24/0.57  thf('0', plain,
% 0.24/0.57      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.24/0.57         ((k2_zfmisc_1 @ (k1_tarski @ X7) @ (k2_tarski @ X8 @ X9))
% 0.24/0.57           = (k2_tarski @ (k4_tarski @ X7 @ X8) @ (k4_tarski @ X7 @ X9)))),
% 0.24/0.57      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.24/0.57  thf(t69_enumset1, axiom,
% 0.24/0.57    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.24/0.57  thf('1', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.24/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.24/0.57  thf('2', plain,
% 0.24/0.57      (![X0 : $i, X1 : $i]:
% 0.24/0.57         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0))
% 0.24/0.57           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.24/0.57      inference('sup+', [status(thm)], ['0', '1'])).
% 0.24/0.57  thf(t195_relat_1, axiom,
% 0.24/0.57    (![A:$i,B:$i]:
% 0.24/0.57     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.24/0.57          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 0.24/0.57               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 0.24/0.57  thf('3', plain,
% 0.24/0.57      (![X11 : $i, X12 : $i]:
% 0.24/0.57         (((X11) = (k1_xboole_0))
% 0.24/0.57          | ((k1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12)) = (X11))
% 0.24/0.57          | ((X12) = (k1_xboole_0)))),
% 0.24/0.57      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.24/0.57  thf('4', plain,
% 0.24/0.57      (![X0 : $i, X1 : $i]:
% 0.24/0.57         (((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.24/0.57            = (k1_tarski @ X1))
% 0.24/0.57          | ((k2_tarski @ X0 @ X0) = (k1_xboole_0))
% 0.24/0.57          | ((k1_tarski @ X1) = (k1_xboole_0)))),
% 0.24/0.57      inference('sup+', [status(thm)], ['2', '3'])).
% 0.24/0.57  thf(fc3_xboole_0, axiom,
% 0.24/0.57    (![A:$i,B:$i]: ( ~( v1_xboole_0 @ ( k2_tarski @ A @ B ) ) ))).
% 0.24/0.57  thf('5', plain,
% 0.24/0.57      (![X3 : $i, X4 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X3 @ X4))),
% 0.24/0.57      inference('cnf', [status(esa)], [fc3_xboole_0])).
% 0.24/0.57  thf('6', plain,
% 0.24/0.57      (![X0 : $i, X1 : $i]:
% 0.24/0.57         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.24/0.57          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.24/0.57          | ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.24/0.57              = (k1_tarski @ X1)))),
% 0.24/0.57      inference('sup-', [status(thm)], ['4', '5'])).
% 0.24/0.57  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.24/0.57  thf('7', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.24/0.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.24/0.57  thf('8', plain,
% 0.24/0.57      (![X0 : $i, X1 : $i]:
% 0.24/0.57         (((k1_tarski @ X1) = (k1_xboole_0))
% 0.24/0.57          | ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.24/0.57              = (k1_tarski @ X1)))),
% 0.24/0.57      inference('demod', [status(thm)], ['6', '7'])).
% 0.24/0.57  thf(d3_mcart_1, axiom,
% 0.24/0.57    (![A:$i,B:$i,C:$i]:
% 0.24/0.57     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.24/0.57  thf('9', plain,
% 0.24/0.57      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.24/0.57         ((k3_mcart_1 @ X13 @ X14 @ X15)
% 0.24/0.57           = (k4_tarski @ (k4_tarski @ X13 @ X14) @ X15))),
% 0.24/0.57      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.24/0.57  thf('10', plain,
% 0.24/0.57      (![X0 : $i, X1 : $i]:
% 0.24/0.57         (((k1_tarski @ X1) = (k1_xboole_0))
% 0.24/0.57          | ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.24/0.57              = (k1_tarski @ X1)))),
% 0.24/0.57      inference('demod', [status(thm)], ['6', '7'])).
% 0.24/0.57  thf('11', plain,
% 0.24/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.57         (((k1_relat_1 @ (k1_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0)))
% 0.24/0.57            = (k1_tarski @ (k4_tarski @ X2 @ X1)))
% 0.24/0.57          | ((k1_tarski @ (k4_tarski @ X2 @ X1)) = (k1_xboole_0)))),
% 0.24/0.57      inference('sup+', [status(thm)], ['9', '10'])).
% 0.24/0.57  thf(t97_mcart_1, conjecture,
% 0.24/0.57    (![A:$i,B:$i,C:$i]:
% 0.24/0.57     ( ( k1_relat_1 @
% 0.24/0.57         ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) ) =
% 0.24/0.57       ( k1_tarski @ A ) ))).
% 0.24/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.24/0.57        ( ( k1_relat_1 @
% 0.24/0.57            ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) ) =
% 0.24/0.57          ( k1_tarski @ A ) ) )),
% 0.24/0.57    inference('cnf.neg', [status(esa)], [t97_mcart_1])).
% 0.24/0.57  thf('12', plain,
% 0.24/0.57      (((k1_relat_1 @ 
% 0.24/0.57         (k1_relat_1 @ (k1_tarski @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C))))
% 0.24/0.57         != (k1_tarski @ sk_A))),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('13', plain,
% 0.24/0.57      ((((k1_relat_1 @ (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))
% 0.24/0.57          != (k1_tarski @ sk_A))
% 0.24/0.57        | ((k1_tarski @ (k4_tarski @ sk_A @ sk_B)) = (k1_xboole_0)))),
% 0.24/0.57      inference('sup-', [status(thm)], ['11', '12'])).
% 0.24/0.57  thf('14', plain,
% 0.24/0.57      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.24/0.57        | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.24/0.57        | ((k1_tarski @ (k4_tarski @ sk_A @ sk_B)) = (k1_xboole_0)))),
% 0.24/0.57      inference('sup-', [status(thm)], ['8', '13'])).
% 0.24/0.57  thf('15', plain,
% 0.24/0.57      ((((k1_tarski @ (k4_tarski @ sk_A @ sk_B)) = (k1_xboole_0))
% 0.24/0.57        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.24/0.57      inference('simplify', [status(thm)], ['14'])).
% 0.24/0.57  thf('16', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.24/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.24/0.57  thf('17', plain,
% 0.24/0.57      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.24/0.57         ((k2_zfmisc_1 @ (k1_tarski @ X7) @ (k2_tarski @ X8 @ X9))
% 0.24/0.57           = (k2_tarski @ (k4_tarski @ X7 @ X8) @ (k4_tarski @ X7 @ X9)))),
% 0.24/0.57      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.24/0.57  thf('18', plain,
% 0.24/0.57      (![X0 : $i, X1 : $i]:
% 0.24/0.57         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.24/0.57           = (k2_tarski @ (k4_tarski @ X1 @ X0) @ (k4_tarski @ X1 @ X0)))),
% 0.24/0.57      inference('sup+', [status(thm)], ['16', '17'])).
% 0.24/0.57  thf('19', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.24/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.24/0.57  thf('20', plain,
% 0.24/0.57      (![X0 : $i, X1 : $i]:
% 0.24/0.57         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.24/0.57           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.24/0.57      inference('demod', [status(thm)], ['18', '19'])).
% 0.24/0.57  thf(t130_zfmisc_1, axiom,
% 0.24/0.57    (![A:$i,B:$i]:
% 0.24/0.57     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.24/0.57       ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.24/0.57         ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.24/0.57  thf('21', plain,
% 0.24/0.57      (![X5 : $i, X6 : $i]:
% 0.24/0.57         (((X5) = (k1_xboole_0))
% 0.24/0.57          | ((k2_zfmisc_1 @ X5 @ (k1_tarski @ X6)) != (k1_xboole_0)))),
% 0.24/0.57      inference('cnf', [status(esa)], [t130_zfmisc_1])).
% 0.24/0.57  thf('22', plain,
% 0.24/0.57      (![X0 : $i, X1 : $i]:
% 0.24/0.57         (((k1_tarski @ (k4_tarski @ X1 @ X0)) != (k1_xboole_0))
% 0.24/0.57          | ((k1_tarski @ X1) = (k1_xboole_0)))),
% 0.24/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.24/0.57  thf('23', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.24/0.57      inference('clc', [status(thm)], ['15', '22'])).
% 0.24/0.57  thf('24', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.24/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.24/0.57  thf('25', plain,
% 0.24/0.57      (![X3 : $i, X4 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X3 @ X4))),
% 0.24/0.57      inference('cnf', [status(esa)], [fc3_xboole_0])).
% 0.24/0.57  thf('26', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.24/0.57      inference('sup-', [status(thm)], ['24', '25'])).
% 0.24/0.57  thf('27', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.24/0.57      inference('sup-', [status(thm)], ['23', '26'])).
% 0.24/0.57  thf('28', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.24/0.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.24/0.57  thf('29', plain, ($false), inference('demod', [status(thm)], ['27', '28'])).
% 0.24/0.57  
% 0.24/0.57  % SZS output end Refutation
% 0.24/0.57  
% 0.24/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
