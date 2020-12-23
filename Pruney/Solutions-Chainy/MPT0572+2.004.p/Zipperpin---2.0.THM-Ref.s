%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iF6mUHgQSp

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:14 EST 2020

% Result     : Theorem 5.44s
% Output     : Refutation 5.44s
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

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

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

thf(t175_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k10_relat_1 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ X18 @ X19 ) @ ( k10_relat_1 @ X18 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t175_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ X1 ) @ ( k10_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k10_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ X1 ) @ ( k10_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k10_relat_1 @ X2 @ X0 ) )
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
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ ( k3_xboole_0 @ ( k10_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ~ ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k10_relat_1 @ X1 @ X2 ) @ ( k10_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k10_relat_1 @ X1 @ X2 ) @ ( k10_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(t176_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( r1_tarski @ ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( r1_tarski @ ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t176_relat_1])).

thf('20',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ) ) ),
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
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iF6mUHgQSp
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:17:40 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 5.44/5.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.44/5.70  % Solved by: fo/fo7.sh
% 5.44/5.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.44/5.70  % done 3635 iterations in 5.249s
% 5.44/5.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.44/5.70  % SZS output start Refutation
% 5.44/5.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.44/5.70  thf(sk_B_type, type, sk_B: $i).
% 5.44/5.70  thf(sk_C_type, type, sk_C: $i).
% 5.44/5.70  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.44/5.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.44/5.70  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 5.44/5.70  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 5.44/5.70  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 5.44/5.70  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 5.44/5.70  thf(sk_A_type, type, sk_A: $i).
% 5.44/5.70  thf(commutativity_k2_tarski, axiom,
% 5.44/5.70    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 5.44/5.70  thf('0', plain,
% 5.44/5.70      (![X9 : $i, X10 : $i]: ((k2_tarski @ X10 @ X9) = (k2_tarski @ X9 @ X10))),
% 5.44/5.70      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 5.44/5.70  thf(t12_setfam_1, axiom,
% 5.44/5.70    (![A:$i,B:$i]:
% 5.44/5.70     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 5.44/5.70  thf('1', plain,
% 5.44/5.70      (![X16 : $i, X17 : $i]:
% 5.44/5.70         ((k1_setfam_1 @ (k2_tarski @ X16 @ X17)) = (k3_xboole_0 @ X16 @ X17))),
% 5.44/5.70      inference('cnf', [status(esa)], [t12_setfam_1])).
% 5.44/5.70  thf('2', plain,
% 5.44/5.70      (![X0 : $i, X1 : $i]:
% 5.44/5.70         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 5.44/5.70      inference('sup+', [status(thm)], ['0', '1'])).
% 5.44/5.70  thf('3', plain,
% 5.44/5.70      (![X16 : $i, X17 : $i]:
% 5.44/5.70         ((k1_setfam_1 @ (k2_tarski @ X16 @ X17)) = (k3_xboole_0 @ X16 @ X17))),
% 5.44/5.70      inference('cnf', [status(esa)], [t12_setfam_1])).
% 5.44/5.70  thf('4', plain,
% 5.44/5.70      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.44/5.70      inference('sup+', [status(thm)], ['2', '3'])).
% 5.44/5.70  thf(t17_xboole_1, axiom,
% 5.44/5.70    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 5.44/5.70  thf('5', plain,
% 5.44/5.70      (![X2 : $i, X3 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ X2)),
% 5.44/5.70      inference('cnf', [status(esa)], [t17_xboole_1])).
% 5.44/5.70  thf(t12_xboole_1, axiom,
% 5.44/5.70    (![A:$i,B:$i]:
% 5.44/5.70     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 5.44/5.70  thf('6', plain,
% 5.44/5.70      (![X0 : $i, X1 : $i]:
% 5.44/5.70         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 5.44/5.70      inference('cnf', [status(esa)], [t12_xboole_1])).
% 5.44/5.70  thf('7', plain,
% 5.44/5.70      (![X0 : $i, X1 : $i]:
% 5.44/5.70         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 5.44/5.70      inference('sup-', [status(thm)], ['5', '6'])).
% 5.44/5.70  thf('8', plain,
% 5.44/5.70      (![X0 : $i, X1 : $i]:
% 5.44/5.70         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 5.44/5.70      inference('sup+', [status(thm)], ['4', '7'])).
% 5.44/5.70  thf(t175_relat_1, axiom,
% 5.44/5.70    (![A:$i,B:$i,C:$i]:
% 5.44/5.70     ( ( v1_relat_1 @ C ) =>
% 5.44/5.70       ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 5.44/5.70         ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 5.44/5.70  thf('9', plain,
% 5.44/5.70      (![X18 : $i, X19 : $i, X20 : $i]:
% 5.44/5.70         (((k10_relat_1 @ X18 @ (k2_xboole_0 @ X19 @ X20))
% 5.44/5.70            = (k2_xboole_0 @ (k10_relat_1 @ X18 @ X19) @ 
% 5.44/5.70               (k10_relat_1 @ X18 @ X20)))
% 5.44/5.70          | ~ (v1_relat_1 @ X18))),
% 5.44/5.70      inference('cnf', [status(esa)], [t175_relat_1])).
% 5.44/5.70  thf(t7_xboole_1, axiom,
% 5.44/5.70    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 5.44/5.70  thf('10', plain,
% 5.44/5.70      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 5.44/5.70      inference('cnf', [status(esa)], [t7_xboole_1])).
% 5.44/5.70  thf('11', plain,
% 5.44/5.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.44/5.70         ((r1_tarski @ (k10_relat_1 @ X2 @ X1) @ 
% 5.44/5.70           (k10_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 5.44/5.70          | ~ (v1_relat_1 @ X2))),
% 5.44/5.70      inference('sup+', [status(thm)], ['9', '10'])).
% 5.44/5.70  thf('12', plain,
% 5.44/5.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.44/5.70         ((r1_tarski @ (k10_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 5.44/5.70           (k10_relat_1 @ X2 @ X0))
% 5.44/5.70          | ~ (v1_relat_1 @ X2))),
% 5.44/5.70      inference('sup+', [status(thm)], ['8', '11'])).
% 5.44/5.70  thf('13', plain,
% 5.44/5.70      (![X0 : $i, X1 : $i]:
% 5.44/5.70         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 5.44/5.70      inference('sup-', [status(thm)], ['5', '6'])).
% 5.44/5.70  thf('14', plain,
% 5.44/5.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.44/5.70         ((r1_tarski @ (k10_relat_1 @ X2 @ X1) @ 
% 5.44/5.70           (k10_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 5.44/5.70          | ~ (v1_relat_1 @ X2))),
% 5.44/5.70      inference('sup+', [status(thm)], ['9', '10'])).
% 5.44/5.70  thf('15', plain,
% 5.44/5.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.44/5.70         ((r1_tarski @ (k10_relat_1 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 5.44/5.70           (k10_relat_1 @ X2 @ X0))
% 5.44/5.70          | ~ (v1_relat_1 @ X2))),
% 5.44/5.70      inference('sup+', [status(thm)], ['13', '14'])).
% 5.44/5.70  thf(t19_xboole_1, axiom,
% 5.44/5.70    (![A:$i,B:$i,C:$i]:
% 5.44/5.70     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 5.44/5.70       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 5.44/5.70  thf('16', plain,
% 5.44/5.70      (![X4 : $i, X5 : $i, X6 : $i]:
% 5.44/5.70         (~ (r1_tarski @ X4 @ X5)
% 5.44/5.70          | ~ (r1_tarski @ X4 @ X6)
% 5.44/5.70          | (r1_tarski @ X4 @ (k3_xboole_0 @ X5 @ X6)))),
% 5.44/5.70      inference('cnf', [status(esa)], [t19_xboole_1])).
% 5.44/5.70  thf('17', plain,
% 5.44/5.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.44/5.70         (~ (v1_relat_1 @ X1)
% 5.44/5.70          | (r1_tarski @ (k10_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ 
% 5.44/5.70             (k3_xboole_0 @ (k10_relat_1 @ X1 @ X0) @ X3))
% 5.44/5.70          | ~ (r1_tarski @ (k10_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ X3))),
% 5.44/5.70      inference('sup-', [status(thm)], ['15', '16'])).
% 5.44/5.70  thf('18', plain,
% 5.44/5.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.44/5.70         (~ (v1_relat_1 @ X1)
% 5.44/5.70          | (r1_tarski @ (k10_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 5.44/5.70             (k3_xboole_0 @ (k10_relat_1 @ X1 @ X2) @ (k10_relat_1 @ X1 @ X0)))
% 5.44/5.70          | ~ (v1_relat_1 @ X1))),
% 5.44/5.70      inference('sup-', [status(thm)], ['12', '17'])).
% 5.44/5.70  thf('19', plain,
% 5.44/5.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.44/5.70         ((r1_tarski @ (k10_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 5.44/5.70           (k3_xboole_0 @ (k10_relat_1 @ X1 @ X2) @ (k10_relat_1 @ X1 @ X0)))
% 5.44/5.70          | ~ (v1_relat_1 @ X1))),
% 5.44/5.70      inference('simplify', [status(thm)], ['18'])).
% 5.44/5.70  thf(t176_relat_1, conjecture,
% 5.44/5.70    (![A:$i,B:$i,C:$i]:
% 5.44/5.70     ( ( v1_relat_1 @ C ) =>
% 5.44/5.70       ( r1_tarski @
% 5.44/5.70         ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 5.44/5.70         ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 5.44/5.70  thf(zf_stmt_0, negated_conjecture,
% 5.44/5.70    (~( ![A:$i,B:$i,C:$i]:
% 5.44/5.70        ( ( v1_relat_1 @ C ) =>
% 5.44/5.70          ( r1_tarski @
% 5.44/5.70            ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 5.44/5.70            ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )),
% 5.44/5.70    inference('cnf.neg', [status(esa)], [t176_relat_1])).
% 5.44/5.70  thf('20', plain,
% 5.44/5.70      (~ (r1_tarski @ (k10_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 5.44/5.70          (k3_xboole_0 @ (k10_relat_1 @ sk_C @ sk_A) @ 
% 5.44/5.70           (k10_relat_1 @ sk_C @ sk_B)))),
% 5.44/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.44/5.70  thf('21', plain, (~ (v1_relat_1 @ sk_C)),
% 5.44/5.70      inference('sup-', [status(thm)], ['19', '20'])).
% 5.44/5.70  thf('22', plain, ((v1_relat_1 @ sk_C)),
% 5.44/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.44/5.70  thf('23', plain, ($false), inference('demod', [status(thm)], ['21', '22'])).
% 5.44/5.70  
% 5.44/5.70  % SZS output end Refutation
% 5.44/5.70  
% 5.54/5.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
