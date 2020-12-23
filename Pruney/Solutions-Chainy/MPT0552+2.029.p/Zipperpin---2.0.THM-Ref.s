%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XZSuX8FinG

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:27 EST 2020

% Result     : Theorem 18.53s
% Output     : Refutation 18.53s
% Verified   : 
% Statistics : Number of formulae       :   49 (  71 expanded)
%              Number of leaves         :   20 (  29 expanded)
%              Depth                    :   12
%              Number of atoms          :  388 ( 626 expanded)
%              Number of equality atoms :   13 (  22 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X6 @ X5 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) )
        = ( k9_relat_1 @ X16 @ X17 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t103_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k7_relat_1 @ C @ A ) ) ) ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( v1_relat_1 @ X15 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X15 @ X14 ) @ X13 )
        = ( k7_relat_1 @ X15 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t103_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
        = ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) )
        = ( k9_relat_1 @ X16 @ X17 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t99_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k2_relat_1 @ B ) ) ) )).

thf('10',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) ) @ ( k2_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t99_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ ( k9_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ ( k9_relat_1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['5','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['4','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(t154_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t154_relat_1])).

thf('24',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['25','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XZSuX8FinG
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:46:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 18.53/18.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 18.53/18.73  % Solved by: fo/fo7.sh
% 18.53/18.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 18.53/18.73  % done 6270 iterations in 18.234s
% 18.53/18.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 18.53/18.73  % SZS output start Refutation
% 18.53/18.73  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 18.53/18.73  thf(sk_C_type, type, sk_C: $i).
% 18.53/18.73  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 18.53/18.73  thf(sk_B_type, type, sk_B: $i).
% 18.53/18.73  thf(sk_A_type, type, sk_A: $i).
% 18.53/18.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 18.53/18.73  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 18.53/18.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 18.53/18.73  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 18.53/18.73  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 18.53/18.73  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 18.53/18.73  thf(commutativity_k2_tarski, axiom,
% 18.53/18.73    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 18.53/18.73  thf('0', plain,
% 18.53/18.73      (![X5 : $i, X6 : $i]: ((k2_tarski @ X6 @ X5) = (k2_tarski @ X5 @ X6))),
% 18.53/18.73      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 18.53/18.73  thf(t12_setfam_1, axiom,
% 18.53/18.73    (![A:$i,B:$i]:
% 18.53/18.73     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 18.53/18.73  thf('1', plain,
% 18.53/18.73      (![X9 : $i, X10 : $i]:
% 18.53/18.73         ((k1_setfam_1 @ (k2_tarski @ X9 @ X10)) = (k3_xboole_0 @ X9 @ X10))),
% 18.53/18.73      inference('cnf', [status(esa)], [t12_setfam_1])).
% 18.53/18.73  thf('2', plain,
% 18.53/18.73      (![X0 : $i, X1 : $i]:
% 18.53/18.73         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 18.53/18.73      inference('sup+', [status(thm)], ['0', '1'])).
% 18.53/18.73  thf('3', plain,
% 18.53/18.73      (![X9 : $i, X10 : $i]:
% 18.53/18.73         ((k1_setfam_1 @ (k2_tarski @ X9 @ X10)) = (k3_xboole_0 @ X9 @ X10))),
% 18.53/18.73      inference('cnf', [status(esa)], [t12_setfam_1])).
% 18.53/18.73  thf('4', plain,
% 18.53/18.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 18.53/18.73      inference('sup+', [status(thm)], ['2', '3'])).
% 18.53/18.73  thf(t148_relat_1, axiom,
% 18.53/18.73    (![A:$i,B:$i]:
% 18.53/18.73     ( ( v1_relat_1 @ B ) =>
% 18.53/18.73       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 18.53/18.73  thf('5', plain,
% 18.53/18.73      (![X16 : $i, X17 : $i]:
% 18.53/18.73         (((k2_relat_1 @ (k7_relat_1 @ X16 @ X17)) = (k9_relat_1 @ X16 @ X17))
% 18.53/18.73          | ~ (v1_relat_1 @ X16))),
% 18.53/18.73      inference('cnf', [status(esa)], [t148_relat_1])).
% 18.53/18.73  thf(t17_xboole_1, axiom,
% 18.53/18.73    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 18.53/18.73  thf('6', plain,
% 18.53/18.73      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 18.53/18.73      inference('cnf', [status(esa)], [t17_xboole_1])).
% 18.53/18.73  thf(t103_relat_1, axiom,
% 18.53/18.73    (![A:$i,B:$i,C:$i]:
% 18.53/18.73     ( ( v1_relat_1 @ C ) =>
% 18.53/18.73       ( ( r1_tarski @ A @ B ) =>
% 18.53/18.73         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k7_relat_1 @ C @ A ) ) ) ))).
% 18.53/18.73  thf('7', plain,
% 18.53/18.73      (![X13 : $i, X14 : $i, X15 : $i]:
% 18.53/18.73         (~ (r1_tarski @ X13 @ X14)
% 18.53/18.73          | ~ (v1_relat_1 @ X15)
% 18.53/18.73          | ((k7_relat_1 @ (k7_relat_1 @ X15 @ X14) @ X13)
% 18.53/18.73              = (k7_relat_1 @ X15 @ X13)))),
% 18.53/18.73      inference('cnf', [status(esa)], [t103_relat_1])).
% 18.53/18.73  thf('8', plain,
% 18.53/18.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.53/18.73         (((k7_relat_1 @ (k7_relat_1 @ X2 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 18.53/18.73            = (k7_relat_1 @ X2 @ (k3_xboole_0 @ X0 @ X1)))
% 18.53/18.73          | ~ (v1_relat_1 @ X2))),
% 18.53/18.73      inference('sup-', [status(thm)], ['6', '7'])).
% 18.53/18.73  thf('9', plain,
% 18.53/18.73      (![X16 : $i, X17 : $i]:
% 18.53/18.73         (((k2_relat_1 @ (k7_relat_1 @ X16 @ X17)) = (k9_relat_1 @ X16 @ X17))
% 18.53/18.73          | ~ (v1_relat_1 @ X16))),
% 18.53/18.73      inference('cnf', [status(esa)], [t148_relat_1])).
% 18.53/18.73  thf(t99_relat_1, axiom,
% 18.53/18.73    (![A:$i,B:$i]:
% 18.53/18.73     ( ( v1_relat_1 @ B ) =>
% 18.53/18.73       ( r1_tarski @
% 18.53/18.73         ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k2_relat_1 @ B ) ) ))).
% 18.53/18.73  thf('10', plain,
% 18.53/18.73      (![X18 : $i, X19 : $i]:
% 18.53/18.73         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X18 @ X19)) @ 
% 18.53/18.73           (k2_relat_1 @ X18))
% 18.53/18.73          | ~ (v1_relat_1 @ X18))),
% 18.53/18.73      inference('cnf', [status(esa)], [t99_relat_1])).
% 18.53/18.73  thf('11', plain,
% 18.53/18.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.53/18.73         ((r1_tarski @ 
% 18.53/18.73           (k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)) @ 
% 18.53/18.73           (k9_relat_1 @ X1 @ X0))
% 18.53/18.73          | ~ (v1_relat_1 @ X1)
% 18.53/18.73          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 18.53/18.73      inference('sup+', [status(thm)], ['9', '10'])).
% 18.53/18.73  thf(dt_k7_relat_1, axiom,
% 18.53/18.73    (![A:$i,B:$i]:
% 18.53/18.73     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 18.53/18.73  thf('12', plain,
% 18.53/18.73      (![X11 : $i, X12 : $i]:
% 18.53/18.73         (~ (v1_relat_1 @ X11) | (v1_relat_1 @ (k7_relat_1 @ X11 @ X12)))),
% 18.53/18.73      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 18.53/18.73  thf('13', plain,
% 18.53/18.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.53/18.73         (~ (v1_relat_1 @ X1)
% 18.53/18.73          | (r1_tarski @ 
% 18.53/18.73             (k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)) @ 
% 18.53/18.73             (k9_relat_1 @ X1 @ X0)))),
% 18.53/18.73      inference('clc', [status(thm)], ['11', '12'])).
% 18.53/18.73  thf('14', plain,
% 18.53/18.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.53/18.73         ((r1_tarski @ 
% 18.53/18.73           (k2_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))) @ 
% 18.53/18.73           (k9_relat_1 @ X2 @ X1))
% 18.53/18.73          | ~ (v1_relat_1 @ X2)
% 18.53/18.73          | ~ (v1_relat_1 @ X2))),
% 18.53/18.73      inference('sup+', [status(thm)], ['8', '13'])).
% 18.53/18.73  thf('15', plain,
% 18.53/18.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.53/18.73         (~ (v1_relat_1 @ X2)
% 18.53/18.73          | (r1_tarski @ 
% 18.53/18.73             (k2_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))) @ 
% 18.53/18.73             (k9_relat_1 @ X2 @ X1)))),
% 18.53/18.73      inference('simplify', [status(thm)], ['14'])).
% 18.53/18.73  thf('16', plain,
% 18.53/18.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.53/18.73         ((r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 18.53/18.73           (k9_relat_1 @ X2 @ X1))
% 18.53/18.73          | ~ (v1_relat_1 @ X2)
% 18.53/18.73          | ~ (v1_relat_1 @ X2))),
% 18.53/18.73      inference('sup+', [status(thm)], ['5', '15'])).
% 18.53/18.73  thf('17', plain,
% 18.53/18.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.53/18.73         (~ (v1_relat_1 @ X2)
% 18.53/18.73          | (r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 18.53/18.73             (k9_relat_1 @ X2 @ X1)))),
% 18.53/18.73      inference('simplify', [status(thm)], ['16'])).
% 18.53/18.73  thf('18', plain,
% 18.53/18.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.53/18.73         ((r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 18.53/18.73           (k9_relat_1 @ X2 @ X0))
% 18.53/18.73          | ~ (v1_relat_1 @ X2))),
% 18.53/18.73      inference('sup+', [status(thm)], ['4', '17'])).
% 18.53/18.73  thf('19', plain,
% 18.53/18.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.53/18.73         (~ (v1_relat_1 @ X2)
% 18.53/18.73          | (r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 18.53/18.73             (k9_relat_1 @ X2 @ X1)))),
% 18.53/18.73      inference('simplify', [status(thm)], ['16'])).
% 18.53/18.73  thf(t19_xboole_1, axiom,
% 18.53/18.73    (![A:$i,B:$i,C:$i]:
% 18.53/18.73     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 18.53/18.73       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 18.53/18.73  thf('20', plain,
% 18.53/18.73      (![X2 : $i, X3 : $i, X4 : $i]:
% 18.53/18.73         (~ (r1_tarski @ X2 @ X3)
% 18.53/18.73          | ~ (r1_tarski @ X2 @ X4)
% 18.53/18.73          | (r1_tarski @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 18.53/18.73      inference('cnf', [status(esa)], [t19_xboole_1])).
% 18.53/18.73  thf('21', plain,
% 18.53/18.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 18.53/18.73         (~ (v1_relat_1 @ X1)
% 18.53/18.73          | (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ 
% 18.53/18.73             (k3_xboole_0 @ (k9_relat_1 @ X1 @ X0) @ X3))
% 18.53/18.73          | ~ (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ X3))),
% 18.53/18.73      inference('sup-', [status(thm)], ['19', '20'])).
% 18.53/18.73  thf('22', plain,
% 18.53/18.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.53/18.73         (~ (v1_relat_1 @ X1)
% 18.53/18.73          | (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 18.53/18.73             (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ (k9_relat_1 @ X1 @ X0)))
% 18.53/18.73          | ~ (v1_relat_1 @ X1))),
% 18.53/18.73      inference('sup-', [status(thm)], ['18', '21'])).
% 18.53/18.73  thf('23', plain,
% 18.53/18.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.53/18.73         ((r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 18.53/18.73           (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ (k9_relat_1 @ X1 @ X0)))
% 18.53/18.73          | ~ (v1_relat_1 @ X1))),
% 18.53/18.73      inference('simplify', [status(thm)], ['22'])).
% 18.53/18.73  thf(t154_relat_1, conjecture,
% 18.53/18.73    (![A:$i,B:$i,C:$i]:
% 18.53/18.73     ( ( v1_relat_1 @ C ) =>
% 18.53/18.73       ( r1_tarski @
% 18.53/18.73         ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 18.53/18.73         ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 18.53/18.73  thf(zf_stmt_0, negated_conjecture,
% 18.53/18.73    (~( ![A:$i,B:$i,C:$i]:
% 18.53/18.73        ( ( v1_relat_1 @ C ) =>
% 18.53/18.73          ( r1_tarski @
% 18.53/18.73            ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 18.53/18.73            ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )),
% 18.53/18.73    inference('cnf.neg', [status(esa)], [t154_relat_1])).
% 18.53/18.73  thf('24', plain,
% 18.53/18.73      (~ (r1_tarski @ (k9_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 18.53/18.73          (k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ 
% 18.53/18.73           (k9_relat_1 @ sk_C @ sk_B)))),
% 18.53/18.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.53/18.73  thf('25', plain, (~ (v1_relat_1 @ sk_C)),
% 18.53/18.73      inference('sup-', [status(thm)], ['23', '24'])).
% 18.53/18.73  thf('26', plain, ((v1_relat_1 @ sk_C)),
% 18.53/18.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.53/18.73  thf('27', plain, ($false), inference('demod', [status(thm)], ['25', '26'])).
% 18.53/18.73  
% 18.53/18.73  % SZS output end Refutation
% 18.53/18.73  
% 18.53/18.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
