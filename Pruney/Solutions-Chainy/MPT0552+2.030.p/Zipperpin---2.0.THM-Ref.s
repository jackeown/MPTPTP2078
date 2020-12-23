%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6ihIxzxnA1

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:27 EST 2020

% Result     : Theorem 6.32s
% Output     : Refutation 6.32s
% Verified   : 
% Statistics : Number of formulae       :   43 (  54 expanded)
%              Number of leaves         :   18 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :  306 ( 410 expanded)
%              Number of equality atoms :   14 (  19 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('0',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_tarski @ X10 @ X9 )
      = ( k2_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(t153_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k9_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k9_relat_1 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) )
        = ( k2_xboole_0 @ ( k9_relat_1 @ X18 @ X19 ) @ ( k9_relat_1 @ X18 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t153_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ X1 ) @ ( k9_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ X1 ) @ ( k9_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k9_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X4 @ X6 )
      | ( r1_tarski @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(t154_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t154_relat_1])).

thf('20',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['21','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6ihIxzxnA1
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:23:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 6.32/6.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.32/6.51  % Solved by: fo/fo7.sh
% 6.32/6.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.32/6.51  % done 3635 iterations in 6.059s
% 6.32/6.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.32/6.51  % SZS output start Refutation
% 6.32/6.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.32/6.51  thf(sk_B_type, type, sk_B: $i).
% 6.32/6.51  thf(sk_C_type, type, sk_C: $i).
% 6.32/6.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 6.32/6.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.32/6.51  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 6.32/6.51  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 6.32/6.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 6.32/6.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 6.32/6.51  thf(sk_A_type, type, sk_A: $i).
% 6.32/6.51  thf(commutativity_k2_tarski, axiom,
% 6.32/6.51    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 6.32/6.51  thf('0', plain,
% 6.32/6.51      (![X9 : $i, X10 : $i]: ((k2_tarski @ X10 @ X9) = (k2_tarski @ X9 @ X10))),
% 6.32/6.51      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 6.32/6.51  thf(t12_setfam_1, axiom,
% 6.32/6.51    (![A:$i,B:$i]:
% 6.32/6.51     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 6.32/6.51  thf('1', plain,
% 6.32/6.51      (![X16 : $i, X17 : $i]:
% 6.32/6.51         ((k1_setfam_1 @ (k2_tarski @ X16 @ X17)) = (k3_xboole_0 @ X16 @ X17))),
% 6.32/6.51      inference('cnf', [status(esa)], [t12_setfam_1])).
% 6.32/6.51  thf('2', plain,
% 6.32/6.51      (![X0 : $i, X1 : $i]:
% 6.32/6.51         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 6.32/6.51      inference('sup+', [status(thm)], ['0', '1'])).
% 6.32/6.51  thf('3', plain,
% 6.32/6.51      (![X16 : $i, X17 : $i]:
% 6.32/6.51         ((k1_setfam_1 @ (k2_tarski @ X16 @ X17)) = (k3_xboole_0 @ X16 @ X17))),
% 6.32/6.51      inference('cnf', [status(esa)], [t12_setfam_1])).
% 6.32/6.51  thf('4', plain,
% 6.32/6.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 6.32/6.51      inference('sup+', [status(thm)], ['2', '3'])).
% 6.32/6.51  thf(t17_xboole_1, axiom,
% 6.32/6.51    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 6.32/6.51  thf('5', plain,
% 6.32/6.51      (![X2 : $i, X3 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ X2)),
% 6.32/6.51      inference('cnf', [status(esa)], [t17_xboole_1])).
% 6.32/6.51  thf(t12_xboole_1, axiom,
% 6.32/6.51    (![A:$i,B:$i]:
% 6.32/6.51     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 6.32/6.51  thf('6', plain,
% 6.32/6.51      (![X0 : $i, X1 : $i]:
% 6.32/6.51         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 6.32/6.51      inference('cnf', [status(esa)], [t12_xboole_1])).
% 6.32/6.51  thf('7', plain,
% 6.32/6.51      (![X0 : $i, X1 : $i]:
% 6.32/6.51         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 6.32/6.51      inference('sup-', [status(thm)], ['5', '6'])).
% 6.32/6.51  thf('8', plain,
% 6.32/6.51      (![X0 : $i, X1 : $i]:
% 6.32/6.51         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 6.32/6.51      inference('sup+', [status(thm)], ['4', '7'])).
% 6.32/6.51  thf(t153_relat_1, axiom,
% 6.32/6.51    (![A:$i,B:$i,C:$i]:
% 6.32/6.51     ( ( v1_relat_1 @ C ) =>
% 6.32/6.51       ( ( k9_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 6.32/6.51         ( k2_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 6.32/6.51  thf('9', plain,
% 6.32/6.51      (![X18 : $i, X19 : $i, X20 : $i]:
% 6.32/6.51         (((k9_relat_1 @ X18 @ (k2_xboole_0 @ X19 @ X20))
% 6.32/6.51            = (k2_xboole_0 @ (k9_relat_1 @ X18 @ X19) @ 
% 6.32/6.51               (k9_relat_1 @ X18 @ X20)))
% 6.32/6.51          | ~ (v1_relat_1 @ X18))),
% 6.32/6.51      inference('cnf', [status(esa)], [t153_relat_1])).
% 6.32/6.51  thf(t7_xboole_1, axiom,
% 6.32/6.51    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 6.32/6.51  thf('10', plain,
% 6.32/6.51      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 6.32/6.51      inference('cnf', [status(esa)], [t7_xboole_1])).
% 6.32/6.51  thf('11', plain,
% 6.32/6.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.32/6.51         ((r1_tarski @ (k9_relat_1 @ X2 @ X1) @ 
% 6.32/6.51           (k9_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 6.32/6.51          | ~ (v1_relat_1 @ X2))),
% 6.32/6.51      inference('sup+', [status(thm)], ['9', '10'])).
% 6.32/6.51  thf('12', plain,
% 6.32/6.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.32/6.51         ((r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 6.32/6.51           (k9_relat_1 @ X2 @ X0))
% 6.32/6.51          | ~ (v1_relat_1 @ X2))),
% 6.32/6.51      inference('sup+', [status(thm)], ['8', '11'])).
% 6.32/6.51  thf('13', plain,
% 6.32/6.51      (![X0 : $i, X1 : $i]:
% 6.32/6.51         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 6.32/6.51      inference('sup-', [status(thm)], ['5', '6'])).
% 6.32/6.51  thf('14', plain,
% 6.32/6.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.32/6.51         ((r1_tarski @ (k9_relat_1 @ X2 @ X1) @ 
% 6.32/6.51           (k9_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 6.32/6.51          | ~ (v1_relat_1 @ X2))),
% 6.32/6.51      inference('sup+', [status(thm)], ['9', '10'])).
% 6.32/6.51  thf('15', plain,
% 6.32/6.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.32/6.51         ((r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 6.32/6.51           (k9_relat_1 @ X2 @ X0))
% 6.32/6.51          | ~ (v1_relat_1 @ X2))),
% 6.32/6.51      inference('sup+', [status(thm)], ['13', '14'])).
% 6.32/6.51  thf(t19_xboole_1, axiom,
% 6.32/6.51    (![A:$i,B:$i,C:$i]:
% 6.32/6.51     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 6.32/6.51       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 6.32/6.51  thf('16', plain,
% 6.32/6.51      (![X4 : $i, X5 : $i, X6 : $i]:
% 6.32/6.51         (~ (r1_tarski @ X4 @ X5)
% 6.32/6.51          | ~ (r1_tarski @ X4 @ X6)
% 6.32/6.51          | (r1_tarski @ X4 @ (k3_xboole_0 @ X5 @ X6)))),
% 6.32/6.51      inference('cnf', [status(esa)], [t19_xboole_1])).
% 6.32/6.51  thf('17', plain,
% 6.32/6.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.32/6.51         (~ (v1_relat_1 @ X1)
% 6.32/6.51          | (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ 
% 6.32/6.51             (k3_xboole_0 @ (k9_relat_1 @ X1 @ X0) @ X3))
% 6.32/6.51          | ~ (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ X3))),
% 6.32/6.51      inference('sup-', [status(thm)], ['15', '16'])).
% 6.32/6.51  thf('18', plain,
% 6.32/6.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.32/6.51         (~ (v1_relat_1 @ X1)
% 6.32/6.51          | (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 6.32/6.51             (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ (k9_relat_1 @ X1 @ X0)))
% 6.32/6.51          | ~ (v1_relat_1 @ X1))),
% 6.32/6.51      inference('sup-', [status(thm)], ['12', '17'])).
% 6.32/6.51  thf('19', plain,
% 6.32/6.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.32/6.51         ((r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 6.32/6.51           (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ (k9_relat_1 @ X1 @ X0)))
% 6.32/6.51          | ~ (v1_relat_1 @ X1))),
% 6.32/6.51      inference('simplify', [status(thm)], ['18'])).
% 6.32/6.51  thf(t154_relat_1, conjecture,
% 6.32/6.51    (![A:$i,B:$i,C:$i]:
% 6.32/6.51     ( ( v1_relat_1 @ C ) =>
% 6.32/6.51       ( r1_tarski @
% 6.32/6.51         ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 6.32/6.51         ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 6.32/6.51  thf(zf_stmt_0, negated_conjecture,
% 6.32/6.51    (~( ![A:$i,B:$i,C:$i]:
% 6.32/6.51        ( ( v1_relat_1 @ C ) =>
% 6.32/6.51          ( r1_tarski @
% 6.32/6.51            ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 6.32/6.51            ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )),
% 6.32/6.51    inference('cnf.neg', [status(esa)], [t154_relat_1])).
% 6.32/6.51  thf('20', plain,
% 6.32/6.51      (~ (r1_tarski @ (k9_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 6.32/6.51          (k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ 
% 6.32/6.51           (k9_relat_1 @ sk_C @ sk_B)))),
% 6.32/6.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.32/6.51  thf('21', plain, (~ (v1_relat_1 @ sk_C)),
% 6.32/6.51      inference('sup-', [status(thm)], ['19', '20'])).
% 6.32/6.51  thf('22', plain, ((v1_relat_1 @ sk_C)),
% 6.32/6.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.32/6.51  thf('23', plain, ($false), inference('demod', [status(thm)], ['21', '22'])).
% 6.32/6.51  
% 6.32/6.51  % SZS output end Refutation
% 6.32/6.51  
% 6.32/6.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
