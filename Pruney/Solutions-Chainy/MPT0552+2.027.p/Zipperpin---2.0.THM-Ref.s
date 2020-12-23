%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.f8qXinbazJ

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:27 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   52 (  65 expanded)
%              Number of leaves         :   19 (  27 expanded)
%              Depth                    :   12
%              Number of atoms          :  445 ( 582 expanded)
%              Number of equality atoms :   19 (  25 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('0',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_tarski @ X4 @ X3 )
      = ( k2_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) @ X13 )
        = ( k7_relat_1 @ X11 @ ( k3_xboole_0 @ X12 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ X1 )
        = ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) )
        = ( k9_relat_1 @ X14 @ X15 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
        = ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
        = ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) )
        = ( k9_relat_1 @ X14 @ X15 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t99_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k2_relat_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) ) @ ( k2_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t99_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) @ X13 )
        = ( k7_relat_1 @ X11 @ ( k3_xboole_0 @ X12 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('18',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) )
        = ( k9_relat_1 @ X14 @ X15 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
        = ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
        = ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X2 )
      | ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf(t154_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t154_relat_1])).

thf('28',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['29','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.f8qXinbazJ
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:05:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.41/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.59  % Solved by: fo/fo7.sh
% 0.41/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.59  % done 242 iterations in 0.142s
% 0.41/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.59  % SZS output start Refutation
% 0.41/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.41/0.59  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.41/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.41/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.59  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.41/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.41/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.59  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.41/0.59  thf(commutativity_k2_tarski, axiom,
% 0.41/0.59    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.41/0.59  thf('0', plain,
% 0.41/0.59      (![X3 : $i, X4 : $i]: ((k2_tarski @ X4 @ X3) = (k2_tarski @ X3 @ X4))),
% 0.41/0.59      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.41/0.59  thf(t12_setfam_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.41/0.59  thf('1', plain,
% 0.41/0.59      (![X7 : $i, X8 : $i]:
% 0.41/0.59         ((k1_setfam_1 @ (k2_tarski @ X7 @ X8)) = (k3_xboole_0 @ X7 @ X8))),
% 0.41/0.59      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.41/0.59  thf('2', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.41/0.59      inference('sup+', [status(thm)], ['0', '1'])).
% 0.41/0.59  thf('3', plain,
% 0.41/0.59      (![X7 : $i, X8 : $i]:
% 0.41/0.59         ((k1_setfam_1 @ (k2_tarski @ X7 @ X8)) = (k3_xboole_0 @ X7 @ X8))),
% 0.41/0.59      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.41/0.59  thf('4', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.41/0.59      inference('sup+', [status(thm)], ['2', '3'])).
% 0.41/0.59  thf(t100_relat_1, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( v1_relat_1 @ C ) =>
% 0.41/0.59       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.41/0.59         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.41/0.59  thf('5', plain,
% 0.41/0.59      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.41/0.59         (((k7_relat_1 @ (k7_relat_1 @ X11 @ X12) @ X13)
% 0.41/0.59            = (k7_relat_1 @ X11 @ (k3_xboole_0 @ X12 @ X13)))
% 0.41/0.59          | ~ (v1_relat_1 @ X11))),
% 0.41/0.59      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.41/0.59  thf('6', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.59         (((k7_relat_1 @ (k7_relat_1 @ X2 @ X0) @ X1)
% 0.41/0.59            = (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.41/0.59          | ~ (v1_relat_1 @ X2))),
% 0.41/0.59      inference('sup+', [status(thm)], ['4', '5'])).
% 0.41/0.59  thf(t148_relat_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( v1_relat_1 @ B ) =>
% 0.41/0.59       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.41/0.59  thf('7', plain,
% 0.41/0.59      (![X14 : $i, X15 : $i]:
% 0.41/0.59         (((k2_relat_1 @ (k7_relat_1 @ X14 @ X15)) = (k9_relat_1 @ X14 @ X15))
% 0.41/0.59          | ~ (v1_relat_1 @ X14))),
% 0.41/0.59      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.41/0.59  thf('8', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.59         (((k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 0.41/0.59            = (k9_relat_1 @ X2 @ (k3_xboole_0 @ X0 @ X1)))
% 0.41/0.59          | ~ (v1_relat_1 @ X2)
% 0.41/0.59          | ~ (v1_relat_1 @ X2))),
% 0.41/0.59      inference('sup+', [status(thm)], ['6', '7'])).
% 0.41/0.59  thf('9', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.59         (~ (v1_relat_1 @ X2)
% 0.41/0.59          | ((k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 0.41/0.59              = (k9_relat_1 @ X2 @ (k3_xboole_0 @ X0 @ X1))))),
% 0.41/0.59      inference('simplify', [status(thm)], ['8'])).
% 0.41/0.59  thf('10', plain,
% 0.41/0.59      (![X14 : $i, X15 : $i]:
% 0.41/0.59         (((k2_relat_1 @ (k7_relat_1 @ X14 @ X15)) = (k9_relat_1 @ X14 @ X15))
% 0.41/0.59          | ~ (v1_relat_1 @ X14))),
% 0.41/0.59      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.41/0.59  thf(t99_relat_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( v1_relat_1 @ B ) =>
% 0.41/0.59       ( r1_tarski @
% 0.41/0.59         ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k2_relat_1 @ B ) ) ))).
% 0.41/0.59  thf('11', plain,
% 0.41/0.59      (![X16 : $i, X17 : $i]:
% 0.41/0.59         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X16 @ X17)) @ 
% 0.41/0.59           (k2_relat_1 @ X16))
% 0.41/0.59          | ~ (v1_relat_1 @ X16))),
% 0.41/0.59      inference('cnf', [status(esa)], [t99_relat_1])).
% 0.41/0.59  thf('12', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.59         ((r1_tarski @ 
% 0.41/0.59           (k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)) @ 
% 0.41/0.59           (k9_relat_1 @ X1 @ X0))
% 0.41/0.59          | ~ (v1_relat_1 @ X1)
% 0.41/0.59          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.41/0.59      inference('sup+', [status(thm)], ['10', '11'])).
% 0.41/0.59  thf(dt_k7_relat_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.41/0.59  thf('13', plain,
% 0.41/0.59      (![X9 : $i, X10 : $i]:
% 0.41/0.59         (~ (v1_relat_1 @ X9) | (v1_relat_1 @ (k7_relat_1 @ X9 @ X10)))),
% 0.41/0.59      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.41/0.59  thf('14', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.59         (~ (v1_relat_1 @ X1)
% 0.41/0.59          | (r1_tarski @ 
% 0.41/0.59             (k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)) @ 
% 0.41/0.59             (k9_relat_1 @ X1 @ X0)))),
% 0.41/0.59      inference('clc', [status(thm)], ['12', '13'])).
% 0.41/0.59  thf('15', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.59         ((r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.41/0.59           (k9_relat_1 @ X2 @ X0))
% 0.41/0.59          | ~ (v1_relat_1 @ X2)
% 0.41/0.59          | ~ (v1_relat_1 @ X2))),
% 0.41/0.59      inference('sup+', [status(thm)], ['9', '14'])).
% 0.41/0.59  thf('16', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.59         (~ (v1_relat_1 @ X2)
% 0.41/0.59          | (r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.41/0.59             (k9_relat_1 @ X2 @ X0)))),
% 0.41/0.59      inference('simplify', [status(thm)], ['15'])).
% 0.41/0.59  thf('17', plain,
% 0.41/0.59      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.41/0.59         (((k7_relat_1 @ (k7_relat_1 @ X11 @ X12) @ X13)
% 0.41/0.59            = (k7_relat_1 @ X11 @ (k3_xboole_0 @ X12 @ X13)))
% 0.41/0.59          | ~ (v1_relat_1 @ X11))),
% 0.41/0.59      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.41/0.59  thf('18', plain,
% 0.41/0.59      (![X14 : $i, X15 : $i]:
% 0.41/0.59         (((k2_relat_1 @ (k7_relat_1 @ X14 @ X15)) = (k9_relat_1 @ X14 @ X15))
% 0.41/0.59          | ~ (v1_relat_1 @ X14))),
% 0.41/0.59      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.41/0.59  thf('19', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.59         (((k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 0.41/0.59            = (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.41/0.59          | ~ (v1_relat_1 @ X2)
% 0.41/0.59          | ~ (v1_relat_1 @ X2))),
% 0.41/0.59      inference('sup+', [status(thm)], ['17', '18'])).
% 0.41/0.59  thf('20', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.59         (~ (v1_relat_1 @ X2)
% 0.41/0.59          | ((k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 0.41/0.59              = (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.41/0.59      inference('simplify', [status(thm)], ['19'])).
% 0.41/0.59  thf('21', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.59         (~ (v1_relat_1 @ X1)
% 0.41/0.59          | (r1_tarski @ 
% 0.41/0.59             (k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)) @ 
% 0.41/0.59             (k9_relat_1 @ X1 @ X0)))),
% 0.41/0.59      inference('clc', [status(thm)], ['12', '13'])).
% 0.41/0.59  thf('22', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.59         ((r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.41/0.59           (k9_relat_1 @ X2 @ X1))
% 0.41/0.59          | ~ (v1_relat_1 @ X2)
% 0.41/0.59          | ~ (v1_relat_1 @ X2))),
% 0.41/0.59      inference('sup+', [status(thm)], ['20', '21'])).
% 0.41/0.59  thf('23', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.59         (~ (v1_relat_1 @ X2)
% 0.41/0.59          | (r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.41/0.59             (k9_relat_1 @ X2 @ X1)))),
% 0.41/0.59      inference('simplify', [status(thm)], ['22'])).
% 0.41/0.59  thf(t19_xboole_1, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.41/0.59       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.41/0.59  thf('24', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.59         (~ (r1_tarski @ X0 @ X1)
% 0.41/0.59          | ~ (r1_tarski @ X0 @ X2)
% 0.41/0.59          | (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.41/0.59      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.41/0.59  thf('25', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.41/0.59         (~ (v1_relat_1 @ X1)
% 0.41/0.59          | (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ 
% 0.41/0.59             (k3_xboole_0 @ (k9_relat_1 @ X1 @ X0) @ X3))
% 0.41/0.59          | ~ (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ X3))),
% 0.41/0.59      inference('sup-', [status(thm)], ['23', '24'])).
% 0.41/0.59  thf('26', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.59         (~ (v1_relat_1 @ X1)
% 0.41/0.59          | (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 0.41/0.59             (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ (k9_relat_1 @ X1 @ X0)))
% 0.41/0.59          | ~ (v1_relat_1 @ X1))),
% 0.41/0.59      inference('sup-', [status(thm)], ['16', '25'])).
% 0.41/0.59  thf('27', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.59         ((r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 0.41/0.59           (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ (k9_relat_1 @ X1 @ X0)))
% 0.41/0.59          | ~ (v1_relat_1 @ X1))),
% 0.41/0.59      inference('simplify', [status(thm)], ['26'])).
% 0.41/0.59  thf(t154_relat_1, conjecture,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( v1_relat_1 @ C ) =>
% 0.41/0.59       ( r1_tarski @
% 0.41/0.59         ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.41/0.59         ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.41/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.59    (~( ![A:$i,B:$i,C:$i]:
% 0.41/0.59        ( ( v1_relat_1 @ C ) =>
% 0.41/0.59          ( r1_tarski @
% 0.41/0.59            ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.41/0.59            ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )),
% 0.41/0.59    inference('cnf.neg', [status(esa)], [t154_relat_1])).
% 0.41/0.59  thf('28', plain,
% 0.41/0.59      (~ (r1_tarski @ (k9_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 0.41/0.59          (k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ 
% 0.41/0.59           (k9_relat_1 @ sk_C @ sk_B)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('29', plain, (~ (v1_relat_1 @ sk_C)),
% 0.41/0.59      inference('sup-', [status(thm)], ['27', '28'])).
% 0.41/0.59  thf('30', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('31', plain, ($false), inference('demod', [status(thm)], ['29', '30'])).
% 0.41/0.59  
% 0.41/0.59  % SZS output end Refutation
% 0.41/0.59  
% 0.41/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
