%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NrooZYeLTr

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   44 (  89 expanded)
%              Number of leaves         :   21 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :  270 ( 605 expanded)
%              Number of equality atoms :   38 (  91 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t97_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_relat_1 @ ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) )
      = ( k1_tarski @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k1_relat_1 @ ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) )
        = ( k1_tarski @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t97_mcart_1])).

thf('0',plain,(
    ( k1_relat_1 @ ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) ) ) )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('1',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( k3_mcart_1 @ X32 @ X33 @ X34 )
      = ( k4_tarski @ ( k4_tarski @ X32 @ X33 ) @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('2',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X24 ) @ ( k2_tarski @ X25 @ X26 ) )
      = ( k2_tarski @ ( k4_tarski @ X24 @ X25 ) @ ( k4_tarski @ X24 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t195_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = A )
            & ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = B ) ) ) )).

thf('5',plain,(
    ! [X30: $i,X31: $i] :
      ( ( X30 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) )
        = X30 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
        = ( k1_tarski @ X1 ) )
      | ( ( k2_tarski @ X0 @ X0 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X21 @ X22 ) )
      = ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('10',plain,(
    ! [X23: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('12',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X28 ) @ X29 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      = ( k1_tarski @ X1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['6','13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) ) )
      = ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      = ( k1_tarski @ X1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['6','13','16'])).

thf('20',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','18','19'])).

thf('21',plain,(
    $false ),
    inference(simplify,[status(thm)],['20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NrooZYeLTr
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:38:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 105 iterations in 0.041s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.50  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.50  thf(t97_mcart_1, conjecture,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( k1_relat_1 @
% 0.21/0.50         ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) ) =
% 0.21/0.50       ( k1_tarski @ A ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.50        ( ( k1_relat_1 @
% 0.21/0.50            ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) ) =
% 0.21/0.50          ( k1_tarski @ A ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t97_mcart_1])).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      (((k1_relat_1 @ 
% 0.21/0.50         (k1_relat_1 @ (k1_tarski @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C))))
% 0.21/0.50         != (k1_tarski @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(d3_mcart_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.21/0.50         ((k3_mcart_1 @ X32 @ X33 @ X34)
% 0.21/0.50           = (k4_tarski @ (k4_tarski @ X32 @ X33) @ X34))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.21/0.50  thf(t36_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 0.21/0.50         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 0.21/0.50       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 0.21/0.50         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.50         ((k2_zfmisc_1 @ (k1_tarski @ X24) @ (k2_tarski @ X25 @ X26))
% 0.21/0.50           = (k2_tarski @ (k4_tarski @ X24 @ X25) @ (k4_tarski @ X24 @ X26)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.21/0.50  thf(t69_enumset1, axiom,
% 0.21/0.50    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.50  thf('3', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0))
% 0.21/0.50           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['2', '3'])).
% 0.21/0.50  thf(t195_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.50          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 0.21/0.50               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X30 : $i, X31 : $i]:
% 0.21/0.50         (((X30) = (k1_xboole_0))
% 0.21/0.50          | ((k1_relat_1 @ (k2_zfmisc_1 @ X30 @ X31)) = (X30))
% 0.21/0.50          | ((X31) = (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.21/0.50            = (k1_tarski @ X1))
% 0.21/0.50          | ((k2_tarski @ X0 @ X0) = (k1_xboole_0))
% 0.21/0.50          | ((k1_tarski @ X1) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['4', '5'])).
% 0.21/0.50  thf('7', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.50  thf(l51_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X21 : $i, X22 : $i]:
% 0.21/0.50         ((k3_tarski @ (k2_tarski @ X21 @ X22)) = (k2_xboole_0 @ X21 @ X22))),
% 0.21/0.50      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['7', '8'])).
% 0.21/0.50  thf(t31_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.21/0.50  thf('10', plain, (![X23 : $i]: ((k3_tarski @ (k1_tarski @ X23)) = (X23))),
% 0.21/0.50      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.21/0.50  thf('11', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.50  thf(t49_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (![X28 : $i, X29 : $i]:
% 0.21/0.50         ((k2_xboole_0 @ (k1_tarski @ X28) @ X29) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.21/0.50  thf('13', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.50  thf('14', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.50  thf('15', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.50  thf('16', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) != (k1_xboole_0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) = (k1_tarski @ X1))),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['6', '13', '16'])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         ((k1_relat_1 @ (k1_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0)))
% 0.21/0.50           = (k1_tarski @ (k4_tarski @ X2 @ X1)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['1', '17'])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) = (k1_tarski @ X1))),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['6', '13', '16'])).
% 0.21/0.50  thf('20', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['0', '18', '19'])).
% 0.21/0.50  thf('21', plain, ($false), inference('simplify', [status(thm)], ['20'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
