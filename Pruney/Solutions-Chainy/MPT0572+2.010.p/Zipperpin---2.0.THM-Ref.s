%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iiDOkAWqo8

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:15 EST 2020

% Result     : Theorem 2.45s
% Output     : Refutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   49 (  67 expanded)
%              Number of leaves         :   18 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :  377 ( 535 expanded)
%              Number of equality atoms :   17 (  28 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('5',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X4 @ X5 ) ) @ X4 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf(t175_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('10',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( ( k10_relat_1 @ X42 @ ( k2_xboole_0 @ X43 @ X44 ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ X42 @ X43 ) @ ( k10_relat_1 @ X42 @ X44 ) ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t175_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ X1 ) @ ( k10_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k10_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ X1 ) @ ( k10_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k10_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X6 @ X8 )
      | ( r1_tarski @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('18',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('19',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X6 @ X8 )
      | ( r1_tarski @ X6 @ ( k1_setfam_1 @ ( k2_tarski @ X7 @ X8 ) ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X2 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k10_relat_1 @ X1 @ X0 ) @ X3 ) ) )
      | ~ ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X2 ) ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X0 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k10_relat_1 @ X1 @ X2 ) @ ( k10_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X0 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k10_relat_1 @ X1 @ X2 ) @ ( k10_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf(t176_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( r1_tarski @ ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( r1_tarski @ ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t176_relat_1])).

thf('23',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('25',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('26',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['22','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['27','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iiDOkAWqo8
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:39:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.45/2.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.45/2.66  % Solved by: fo/fo7.sh
% 2.45/2.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.45/2.66  % done 2183 iterations in 2.199s
% 2.45/2.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.45/2.66  % SZS output start Refutation
% 2.45/2.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.45/2.66  thf(sk_C_type, type, sk_C: $i).
% 2.45/2.66  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 2.45/2.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.45/2.66  thf(sk_A_type, type, sk_A: $i).
% 2.45/2.66  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 2.45/2.66  thf(sk_B_type, type, sk_B: $i).
% 2.45/2.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.45/2.66  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.45/2.66  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.45/2.66  thf(commutativity_k3_xboole_0, axiom,
% 2.45/2.66    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.45/2.66  thf('0', plain,
% 2.45/2.66      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.45/2.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.45/2.66  thf(t12_setfam_1, axiom,
% 2.45/2.66    (![A:$i,B:$i]:
% 2.45/2.66     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.45/2.66  thf('1', plain,
% 2.45/2.66      (![X40 : $i, X41 : $i]:
% 2.45/2.66         ((k1_setfam_1 @ (k2_tarski @ X40 @ X41)) = (k3_xboole_0 @ X40 @ X41))),
% 2.45/2.66      inference('cnf', [status(esa)], [t12_setfam_1])).
% 2.45/2.66  thf('2', plain,
% 2.45/2.66      (![X40 : $i, X41 : $i]:
% 2.45/2.66         ((k1_setfam_1 @ (k2_tarski @ X40 @ X41)) = (k3_xboole_0 @ X40 @ X41))),
% 2.45/2.66      inference('cnf', [status(esa)], [t12_setfam_1])).
% 2.45/2.66  thf('3', plain,
% 2.45/2.66      (![X0 : $i, X1 : $i]:
% 2.45/2.66         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 2.45/2.66           = (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))),
% 2.45/2.66      inference('demod', [status(thm)], ['0', '1', '2'])).
% 2.45/2.66  thf(t17_xboole_1, axiom,
% 2.45/2.66    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 2.45/2.66  thf('4', plain,
% 2.45/2.66      (![X4 : $i, X5 : $i]: (r1_tarski @ (k3_xboole_0 @ X4 @ X5) @ X4)),
% 2.45/2.66      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.45/2.66  thf('5', plain,
% 2.45/2.66      (![X40 : $i, X41 : $i]:
% 2.45/2.66         ((k1_setfam_1 @ (k2_tarski @ X40 @ X41)) = (k3_xboole_0 @ X40 @ X41))),
% 2.45/2.66      inference('cnf', [status(esa)], [t12_setfam_1])).
% 2.45/2.66  thf('6', plain,
% 2.45/2.66      (![X4 : $i, X5 : $i]:
% 2.45/2.66         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X4 @ X5)) @ X4)),
% 2.45/2.66      inference('demod', [status(thm)], ['4', '5'])).
% 2.45/2.66  thf(t12_xboole_1, axiom,
% 2.45/2.66    (![A:$i,B:$i]:
% 2.45/2.66     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 2.45/2.66  thf('7', plain,
% 2.45/2.66      (![X2 : $i, X3 : $i]:
% 2.45/2.66         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 2.45/2.66      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.45/2.66  thf('8', plain,
% 2.45/2.66      (![X0 : $i, X1 : $i]:
% 2.45/2.66         ((k2_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0) = (X0))),
% 2.45/2.66      inference('sup-', [status(thm)], ['6', '7'])).
% 2.45/2.66  thf('9', plain,
% 2.45/2.66      (![X0 : $i, X1 : $i]:
% 2.45/2.66         ((k2_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0) = (X0))),
% 2.45/2.66      inference('sup+', [status(thm)], ['3', '8'])).
% 2.45/2.66  thf(t175_relat_1, axiom,
% 2.45/2.66    (![A:$i,B:$i,C:$i]:
% 2.45/2.66     ( ( v1_relat_1 @ C ) =>
% 2.45/2.66       ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 2.45/2.66         ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 2.45/2.66  thf('10', plain,
% 2.45/2.66      (![X42 : $i, X43 : $i, X44 : $i]:
% 2.45/2.66         (((k10_relat_1 @ X42 @ (k2_xboole_0 @ X43 @ X44))
% 2.45/2.66            = (k2_xboole_0 @ (k10_relat_1 @ X42 @ X43) @ 
% 2.45/2.66               (k10_relat_1 @ X42 @ X44)))
% 2.45/2.66          | ~ (v1_relat_1 @ X42))),
% 2.45/2.66      inference('cnf', [status(esa)], [t175_relat_1])).
% 2.45/2.66  thf(t7_xboole_1, axiom,
% 2.45/2.66    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 2.45/2.66  thf('11', plain,
% 2.45/2.66      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 2.45/2.66      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.45/2.66  thf('12', plain,
% 2.45/2.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.45/2.66         ((r1_tarski @ (k10_relat_1 @ X2 @ X1) @ 
% 2.45/2.66           (k10_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 2.45/2.66          | ~ (v1_relat_1 @ X2))),
% 2.45/2.66      inference('sup+', [status(thm)], ['10', '11'])).
% 2.45/2.66  thf('13', plain,
% 2.45/2.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.45/2.66         ((r1_tarski @ 
% 2.45/2.66           (k10_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 2.45/2.66           (k10_relat_1 @ X2 @ X0))
% 2.45/2.66          | ~ (v1_relat_1 @ X2))),
% 2.45/2.66      inference('sup+', [status(thm)], ['9', '12'])).
% 2.45/2.66  thf('14', plain,
% 2.45/2.66      (![X0 : $i, X1 : $i]:
% 2.45/2.66         ((k2_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0) = (X0))),
% 2.45/2.66      inference('sup-', [status(thm)], ['6', '7'])).
% 2.45/2.66  thf('15', plain,
% 2.45/2.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.45/2.66         ((r1_tarski @ (k10_relat_1 @ X2 @ X1) @ 
% 2.45/2.66           (k10_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 2.45/2.66          | ~ (v1_relat_1 @ X2))),
% 2.45/2.66      inference('sup+', [status(thm)], ['10', '11'])).
% 2.45/2.66  thf('16', plain,
% 2.45/2.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.45/2.66         ((r1_tarski @ 
% 2.45/2.66           (k10_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 2.45/2.66           (k10_relat_1 @ X2 @ X0))
% 2.45/2.66          | ~ (v1_relat_1 @ X2))),
% 2.45/2.66      inference('sup+', [status(thm)], ['14', '15'])).
% 2.45/2.66  thf(t19_xboole_1, axiom,
% 2.45/2.66    (![A:$i,B:$i,C:$i]:
% 2.45/2.66     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 2.45/2.66       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 2.45/2.66  thf('17', plain,
% 2.45/2.66      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.45/2.66         (~ (r1_tarski @ X6 @ X7)
% 2.45/2.66          | ~ (r1_tarski @ X6 @ X8)
% 2.45/2.66          | (r1_tarski @ X6 @ (k3_xboole_0 @ X7 @ X8)))),
% 2.45/2.66      inference('cnf', [status(esa)], [t19_xboole_1])).
% 2.45/2.66  thf('18', plain,
% 2.45/2.66      (![X40 : $i, X41 : $i]:
% 2.45/2.66         ((k1_setfam_1 @ (k2_tarski @ X40 @ X41)) = (k3_xboole_0 @ X40 @ X41))),
% 2.45/2.66      inference('cnf', [status(esa)], [t12_setfam_1])).
% 2.45/2.66  thf('19', plain,
% 2.45/2.66      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.45/2.66         (~ (r1_tarski @ X6 @ X7)
% 2.45/2.66          | ~ (r1_tarski @ X6 @ X8)
% 2.45/2.66          | (r1_tarski @ X6 @ (k1_setfam_1 @ (k2_tarski @ X7 @ X8))))),
% 2.45/2.66      inference('demod', [status(thm)], ['17', '18'])).
% 2.45/2.66  thf('20', plain,
% 2.45/2.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.45/2.66         (~ (v1_relat_1 @ X1)
% 2.45/2.66          | (r1_tarski @ 
% 2.45/2.66             (k10_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X2))) @ 
% 2.45/2.66             (k1_setfam_1 @ (k2_tarski @ (k10_relat_1 @ X1 @ X0) @ X3)))
% 2.45/2.66          | ~ (r1_tarski @ 
% 2.45/2.66               (k10_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X2))) @ X3))),
% 2.45/2.66      inference('sup-', [status(thm)], ['16', '19'])).
% 2.45/2.66  thf('21', plain,
% 2.45/2.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.45/2.66         (~ (v1_relat_1 @ X1)
% 2.45/2.66          | (r1_tarski @ 
% 2.45/2.66             (k10_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X2 @ X0))) @ 
% 2.45/2.66             (k1_setfam_1 @ 
% 2.45/2.66              (k2_tarski @ (k10_relat_1 @ X1 @ X2) @ (k10_relat_1 @ X1 @ X0))))
% 2.45/2.66          | ~ (v1_relat_1 @ X1))),
% 2.45/2.66      inference('sup-', [status(thm)], ['13', '20'])).
% 2.45/2.66  thf('22', plain,
% 2.45/2.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.45/2.66         ((r1_tarski @ 
% 2.45/2.66           (k10_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X2 @ X0))) @ 
% 2.45/2.66           (k1_setfam_1 @ 
% 2.45/2.66            (k2_tarski @ (k10_relat_1 @ X1 @ X2) @ (k10_relat_1 @ X1 @ X0))))
% 2.45/2.66          | ~ (v1_relat_1 @ X1))),
% 2.45/2.66      inference('simplify', [status(thm)], ['21'])).
% 2.45/2.66  thf(t176_relat_1, conjecture,
% 2.45/2.66    (![A:$i,B:$i,C:$i]:
% 2.45/2.66     ( ( v1_relat_1 @ C ) =>
% 2.45/2.66       ( r1_tarski @
% 2.45/2.66         ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 2.45/2.66         ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 2.45/2.66  thf(zf_stmt_0, negated_conjecture,
% 2.45/2.66    (~( ![A:$i,B:$i,C:$i]:
% 2.45/2.66        ( ( v1_relat_1 @ C ) =>
% 2.45/2.66          ( r1_tarski @
% 2.45/2.66            ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 2.45/2.66            ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )),
% 2.45/2.66    inference('cnf.neg', [status(esa)], [t176_relat_1])).
% 2.45/2.66  thf('23', plain,
% 2.45/2.66      (~ (r1_tarski @ (k10_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 2.45/2.66          (k3_xboole_0 @ (k10_relat_1 @ sk_C @ sk_A) @ 
% 2.45/2.66           (k10_relat_1 @ sk_C @ sk_B)))),
% 2.45/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.45/2.66  thf('24', plain,
% 2.45/2.66      (![X40 : $i, X41 : $i]:
% 2.45/2.66         ((k1_setfam_1 @ (k2_tarski @ X40 @ X41)) = (k3_xboole_0 @ X40 @ X41))),
% 2.45/2.66      inference('cnf', [status(esa)], [t12_setfam_1])).
% 2.45/2.66  thf('25', plain,
% 2.45/2.66      (![X40 : $i, X41 : $i]:
% 2.45/2.66         ((k1_setfam_1 @ (k2_tarski @ X40 @ X41)) = (k3_xboole_0 @ X40 @ X41))),
% 2.45/2.66      inference('cnf', [status(esa)], [t12_setfam_1])).
% 2.45/2.66  thf('26', plain,
% 2.45/2.66      (~ (r1_tarski @ 
% 2.45/2.66          (k10_relat_1 @ sk_C @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))) @ 
% 2.45/2.66          (k1_setfam_1 @ 
% 2.45/2.66           (k2_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ 
% 2.45/2.66            (k10_relat_1 @ sk_C @ sk_B))))),
% 2.45/2.66      inference('demod', [status(thm)], ['23', '24', '25'])).
% 2.45/2.66  thf('27', plain, (~ (v1_relat_1 @ sk_C)),
% 2.45/2.66      inference('sup-', [status(thm)], ['22', '26'])).
% 2.45/2.66  thf('28', plain, ((v1_relat_1 @ sk_C)),
% 2.45/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.45/2.66  thf('29', plain, ($false), inference('demod', [status(thm)], ['27', '28'])).
% 2.45/2.66  
% 2.45/2.66  % SZS output end Refutation
% 2.45/2.66  
% 2.45/2.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
