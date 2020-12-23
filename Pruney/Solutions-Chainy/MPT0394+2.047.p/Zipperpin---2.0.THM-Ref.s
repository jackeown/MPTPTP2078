%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EpZ76IxoYz

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:51 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   46 (  59 expanded)
%              Number of leaves         :   19 (  26 expanded)
%              Depth                    :   12
%              Number of atoms          :  288 ( 367 expanded)
%              Number of equality atoms :   44 (  57 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(t12_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
        = ( k3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_setfam_1])).

thf('0',plain,(
    ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X17 @ X17 @ X18 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t43_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X4 @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X5 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('3',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('4',plain,(
    ! [X29: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) )
         != ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) )).

thf('6',plain,(
    ! [X27: $i,X28: $i] :
      ( ( X27 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ X27 @ X28 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X27 ) @ ( k1_setfam_1 @ X28 ) ) )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t10_setfam_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ ( k1_setfam_1 @ X1 ) ) )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_tarski @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('9',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X22 @ X23 ) )
      = ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('12',plain,(
    ! [X24: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('14',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X25 ) @ X26 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ ( k1_setfam_1 @ X1 ) ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['7','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['2','17'])).

thf('19',plain,(
    ! [X29: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','22'])).

thf('24',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','23'])).

thf('25',plain,(
    $false ),
    inference(simplify,[status(thm)],['24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EpZ76IxoYz
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:35:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 207 iterations in 0.069s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.52  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.22/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.52  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.22/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.52  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.22/0.52  thf(t12_setfam_1, conjecture,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i,B:$i]:
% 0.22/0.52        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t12_setfam_1])).
% 0.22/0.52  thf('0', plain,
% 0.22/0.52      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.22/0.52         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t70_enumset1, axiom,
% 0.22/0.52    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      (![X17 : $i, X18 : $i]:
% 0.22/0.52         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 0.22/0.52      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.52  thf(t43_enumset1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.22/0.52       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ))).
% 0.22/0.52  thf('2', plain,
% 0.22/0.52      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.52         ((k1_enumset1 @ X4 @ X5 @ X6)
% 0.22/0.52           = (k2_xboole_0 @ (k2_tarski @ X4 @ X5) @ (k1_tarski @ X6)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.22/0.52  thf(t69_enumset1, axiom,
% 0.22/0.52    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.52  thf('3', plain, (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.22/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.52  thf(t11_setfam_1, axiom,
% 0.22/0.52    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.22/0.52  thf('4', plain, (![X29 : $i]: ((k1_setfam_1 @ (k1_tarski @ X29)) = (X29))),
% 0.22/0.52      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.22/0.52  thf('5', plain, (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['3', '4'])).
% 0.22/0.52  thf(t10_setfam_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.52          ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) ) !=
% 0.22/0.52            ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) ))).
% 0.22/0.52  thf('6', plain,
% 0.22/0.52      (![X27 : $i, X28 : $i]:
% 0.22/0.52         (((X27) = (k1_xboole_0))
% 0.22/0.52          | ((k1_setfam_1 @ (k2_xboole_0 @ X27 @ X28))
% 0.22/0.52              = (k3_xboole_0 @ (k1_setfam_1 @ X27) @ (k1_setfam_1 @ X28)))
% 0.22/0.52          | ((X28) = (k1_xboole_0)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t10_setfam_1])).
% 0.22/0.52  thf('7', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (((k1_setfam_1 @ (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ X1))
% 0.22/0.52            = (k3_xboole_0 @ X0 @ (k1_setfam_1 @ X1)))
% 0.22/0.52          | ((X1) = (k1_xboole_0))
% 0.22/0.52          | ((k2_tarski @ X0 @ X0) = (k1_xboole_0)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['5', '6'])).
% 0.22/0.52  thf('8', plain, (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.22/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.52  thf('9', plain, (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.22/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.52  thf(l51_zfmisc_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.52  thf('10', plain,
% 0.22/0.52      (![X22 : $i, X23 : $i]:
% 0.22/0.52         ((k3_tarski @ (k2_tarski @ X22 @ X23)) = (k2_xboole_0 @ X22 @ X23))),
% 0.22/0.52      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.22/0.52  thf('11', plain,
% 0.22/0.52      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['9', '10'])).
% 0.22/0.52  thf(t31_zfmisc_1, axiom,
% 0.22/0.52    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.22/0.52  thf('12', plain, (![X24 : $i]: ((k3_tarski @ (k1_tarski @ X24)) = (X24))),
% 0.22/0.52      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.22/0.52  thf('13', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 0.22/0.52      inference('demod', [status(thm)], ['11', '12'])).
% 0.22/0.52  thf(t49_zfmisc_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.22/0.52  thf('14', plain,
% 0.22/0.52      (![X25 : $i, X26 : $i]:
% 0.22/0.52         ((k2_xboole_0 @ (k1_tarski @ X25) @ X26) != (k1_xboole_0))),
% 0.22/0.52      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.22/0.52  thf('15', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.52  thf('16', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) != (k1_xboole_0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['8', '15'])).
% 0.22/0.52  thf('17', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (((k1_setfam_1 @ (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ X1))
% 0.22/0.52            = (k3_xboole_0 @ X0 @ (k1_setfam_1 @ X1)))
% 0.22/0.52          | ((X1) = (k1_xboole_0)))),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['7', '16'])).
% 0.22/0.52  thf('18', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (((k1_setfam_1 @ (k1_enumset1 @ X1 @ X1 @ X0))
% 0.22/0.52            = (k3_xboole_0 @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0))))
% 0.22/0.52          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['2', '17'])).
% 0.22/0.52  thf('19', plain, (![X29 : $i]: ((k1_setfam_1 @ (k1_tarski @ X29)) = (X29))),
% 0.22/0.52      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.22/0.52  thf('20', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (((k1_setfam_1 @ (k1_enumset1 @ X1 @ X1 @ X0))
% 0.22/0.52            = (k3_xboole_0 @ X1 @ X0))
% 0.22/0.52          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.22/0.52      inference('demod', [status(thm)], ['18', '19'])).
% 0.22/0.52  thf('21', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.52  thf('22', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((k1_setfam_1 @ (k1_enumset1 @ X1 @ X1 @ X0))
% 0.22/0.52           = (k3_xboole_0 @ X1 @ X0))),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['20', '21'])).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['1', '22'])).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      (((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['0', '23'])).
% 0.22/0.52  thf('25', plain, ($false), inference('simplify', [status(thm)], ['24'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
