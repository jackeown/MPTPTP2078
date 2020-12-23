%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5VzEYlTWVB

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:27 EST 2020

% Result     : Theorem 15.68s
% Output     : Refutation 15.68s
% Verified   : 
% Statistics : Number of formulae       :   53 (  83 expanded)
%              Number of leaves         :   20 (  33 expanded)
%              Depth                    :   13
%              Number of atoms          :  436 ( 754 expanded)
%              Number of equality atoms :   16 (  30 expanded)
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

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X18: $i,X19: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) )
        = ( k9_relat_1 @ X18 @ X19 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) )
        = ( k9_relat_1 @ X18 @ X19 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) )
        = ( k9_relat_1 @ X18 @ X19 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('14',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X16 @ X17 ) @ ( k2_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ ( k9_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ ( k9_relat_1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['5','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['4','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
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
    inference('sup-',[status(thm)],['22','25'])).

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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5VzEYlTWVB
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:19:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 15.68/15.86  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 15.68/15.86  % Solved by: fo/fo7.sh
% 15.68/15.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 15.68/15.86  % done 3797 iterations in 15.408s
% 15.68/15.86  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 15.68/15.86  % SZS output start Refutation
% 15.68/15.86  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 15.68/15.86  thf(sk_C_type, type, sk_C: $i).
% 15.68/15.86  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 15.68/15.86  thf(sk_B_type, type, sk_B: $i).
% 15.68/15.86  thf(sk_A_type, type, sk_A: $i).
% 15.68/15.86  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 15.68/15.86  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 15.68/15.86  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 15.68/15.86  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 15.68/15.86  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 15.68/15.86  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 15.68/15.86  thf(commutativity_k2_tarski, axiom,
% 15.68/15.86    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 15.68/15.86  thf('0', plain,
% 15.68/15.86      (![X5 : $i, X6 : $i]: ((k2_tarski @ X6 @ X5) = (k2_tarski @ X5 @ X6))),
% 15.68/15.86      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 15.68/15.86  thf(t12_setfam_1, axiom,
% 15.68/15.86    (![A:$i,B:$i]:
% 15.68/15.86     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 15.68/15.86  thf('1', plain,
% 15.68/15.86      (![X9 : $i, X10 : $i]:
% 15.68/15.86         ((k1_setfam_1 @ (k2_tarski @ X9 @ X10)) = (k3_xboole_0 @ X9 @ X10))),
% 15.68/15.86      inference('cnf', [status(esa)], [t12_setfam_1])).
% 15.68/15.86  thf('2', plain,
% 15.68/15.86      (![X0 : $i, X1 : $i]:
% 15.68/15.86         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 15.68/15.86      inference('sup+', [status(thm)], ['0', '1'])).
% 15.68/15.86  thf('3', plain,
% 15.68/15.86      (![X9 : $i, X10 : $i]:
% 15.68/15.86         ((k1_setfam_1 @ (k2_tarski @ X9 @ X10)) = (k3_xboole_0 @ X9 @ X10))),
% 15.68/15.86      inference('cnf', [status(esa)], [t12_setfam_1])).
% 15.68/15.86  thf('4', plain,
% 15.68/15.86      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 15.68/15.86      inference('sup+', [status(thm)], ['2', '3'])).
% 15.68/15.86  thf(t148_relat_1, axiom,
% 15.68/15.86    (![A:$i,B:$i]:
% 15.68/15.86     ( ( v1_relat_1 @ B ) =>
% 15.68/15.86       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 15.68/15.86  thf('5', plain,
% 15.68/15.86      (![X18 : $i, X19 : $i]:
% 15.68/15.86         (((k2_relat_1 @ (k7_relat_1 @ X18 @ X19)) = (k9_relat_1 @ X18 @ X19))
% 15.68/15.86          | ~ (v1_relat_1 @ X18))),
% 15.68/15.86      inference('cnf', [status(esa)], [t148_relat_1])).
% 15.68/15.86  thf(t17_xboole_1, axiom,
% 15.68/15.86    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 15.68/15.86  thf('6', plain,
% 15.68/15.86      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 15.68/15.86      inference('cnf', [status(esa)], [t17_xboole_1])).
% 15.68/15.86  thf(t103_relat_1, axiom,
% 15.68/15.86    (![A:$i,B:$i,C:$i]:
% 15.68/15.86     ( ( v1_relat_1 @ C ) =>
% 15.68/15.86       ( ( r1_tarski @ A @ B ) =>
% 15.68/15.86         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k7_relat_1 @ C @ A ) ) ) ))).
% 15.68/15.86  thf('7', plain,
% 15.68/15.86      (![X13 : $i, X14 : $i, X15 : $i]:
% 15.68/15.86         (~ (r1_tarski @ X13 @ X14)
% 15.68/15.86          | ~ (v1_relat_1 @ X15)
% 15.68/15.86          | ((k7_relat_1 @ (k7_relat_1 @ X15 @ X14) @ X13)
% 15.68/15.86              = (k7_relat_1 @ X15 @ X13)))),
% 15.68/15.86      inference('cnf', [status(esa)], [t103_relat_1])).
% 15.68/15.86  thf('8', plain,
% 15.68/15.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.68/15.86         (((k7_relat_1 @ (k7_relat_1 @ X2 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 15.68/15.86            = (k7_relat_1 @ X2 @ (k3_xboole_0 @ X0 @ X1)))
% 15.68/15.86          | ~ (v1_relat_1 @ X2))),
% 15.68/15.86      inference('sup-', [status(thm)], ['6', '7'])).
% 15.68/15.86  thf('9', plain,
% 15.68/15.86      (![X18 : $i, X19 : $i]:
% 15.68/15.86         (((k2_relat_1 @ (k7_relat_1 @ X18 @ X19)) = (k9_relat_1 @ X18 @ X19))
% 15.68/15.86          | ~ (v1_relat_1 @ X18))),
% 15.68/15.86      inference('cnf', [status(esa)], [t148_relat_1])).
% 15.68/15.86  thf('10', plain,
% 15.68/15.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.68/15.86         (((k2_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 15.68/15.86            = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ (k3_xboole_0 @ X1 @ X0)))
% 15.68/15.86          | ~ (v1_relat_1 @ X2)
% 15.68/15.86          | ~ (v1_relat_1 @ (k7_relat_1 @ X2 @ X1)))),
% 15.68/15.86      inference('sup+', [status(thm)], ['8', '9'])).
% 15.68/15.86  thf(dt_k7_relat_1, axiom,
% 15.68/15.86    (![A:$i,B:$i]:
% 15.68/15.86     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 15.68/15.86  thf('11', plain,
% 15.68/15.86      (![X11 : $i, X12 : $i]:
% 15.68/15.86         (~ (v1_relat_1 @ X11) | (v1_relat_1 @ (k7_relat_1 @ X11 @ X12)))),
% 15.68/15.86      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 15.68/15.86  thf('12', plain,
% 15.68/15.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.68/15.86         (~ (v1_relat_1 @ X2)
% 15.68/15.86          | ((k2_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 15.68/15.86              = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ (k3_xboole_0 @ X1 @ X0))))),
% 15.68/15.86      inference('clc', [status(thm)], ['10', '11'])).
% 15.68/15.86  thf('13', plain,
% 15.68/15.86      (![X18 : $i, X19 : $i]:
% 15.68/15.86         (((k2_relat_1 @ (k7_relat_1 @ X18 @ X19)) = (k9_relat_1 @ X18 @ X19))
% 15.68/15.86          | ~ (v1_relat_1 @ X18))),
% 15.68/15.86      inference('cnf', [status(esa)], [t148_relat_1])).
% 15.68/15.86  thf(t144_relat_1, axiom,
% 15.68/15.86    (![A:$i,B:$i]:
% 15.68/15.86     ( ( v1_relat_1 @ B ) =>
% 15.68/15.86       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 15.68/15.86  thf('14', plain,
% 15.68/15.86      (![X16 : $i, X17 : $i]:
% 15.68/15.86         ((r1_tarski @ (k9_relat_1 @ X16 @ X17) @ (k2_relat_1 @ X16))
% 15.68/15.86          | ~ (v1_relat_1 @ X16))),
% 15.68/15.86      inference('cnf', [status(esa)], [t144_relat_1])).
% 15.68/15.86  thf('15', plain,
% 15.68/15.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.68/15.86         ((r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 15.68/15.86           (k9_relat_1 @ X1 @ X0))
% 15.68/15.86          | ~ (v1_relat_1 @ X1)
% 15.68/15.86          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 15.68/15.86      inference('sup+', [status(thm)], ['13', '14'])).
% 15.68/15.86  thf('16', plain,
% 15.68/15.86      (![X11 : $i, X12 : $i]:
% 15.68/15.86         (~ (v1_relat_1 @ X11) | (v1_relat_1 @ (k7_relat_1 @ X11 @ X12)))),
% 15.68/15.86      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 15.68/15.86  thf('17', plain,
% 15.68/15.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.68/15.86         (~ (v1_relat_1 @ X1)
% 15.68/15.86          | (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 15.68/15.86             (k9_relat_1 @ X1 @ X0)))),
% 15.68/15.86      inference('clc', [status(thm)], ['15', '16'])).
% 15.68/15.86  thf('18', plain,
% 15.68/15.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.68/15.86         ((r1_tarski @ 
% 15.68/15.86           (k2_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))) @ 
% 15.68/15.86           (k9_relat_1 @ X2 @ X1))
% 15.68/15.86          | ~ (v1_relat_1 @ X2)
% 15.68/15.86          | ~ (v1_relat_1 @ X2))),
% 15.68/15.86      inference('sup+', [status(thm)], ['12', '17'])).
% 15.68/15.86  thf('19', plain,
% 15.68/15.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.68/15.86         (~ (v1_relat_1 @ X2)
% 15.68/15.86          | (r1_tarski @ 
% 15.68/15.86             (k2_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))) @ 
% 15.68/15.86             (k9_relat_1 @ X2 @ X1)))),
% 15.68/15.86      inference('simplify', [status(thm)], ['18'])).
% 15.68/15.86  thf('20', plain,
% 15.68/15.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.68/15.86         ((r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 15.68/15.86           (k9_relat_1 @ X2 @ X1))
% 15.68/15.86          | ~ (v1_relat_1 @ X2)
% 15.68/15.86          | ~ (v1_relat_1 @ X2))),
% 15.68/15.86      inference('sup+', [status(thm)], ['5', '19'])).
% 15.68/15.86  thf('21', plain,
% 15.68/15.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.68/15.86         (~ (v1_relat_1 @ X2)
% 15.68/15.86          | (r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 15.68/15.86             (k9_relat_1 @ X2 @ X1)))),
% 15.68/15.86      inference('simplify', [status(thm)], ['20'])).
% 15.68/15.86  thf('22', plain,
% 15.68/15.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.68/15.86         ((r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 15.68/15.86           (k9_relat_1 @ X2 @ X0))
% 15.68/15.86          | ~ (v1_relat_1 @ X2))),
% 15.68/15.86      inference('sup+', [status(thm)], ['4', '21'])).
% 15.68/15.86  thf('23', plain,
% 15.68/15.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.68/15.86         (~ (v1_relat_1 @ X2)
% 15.68/15.86          | (r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 15.68/15.86             (k9_relat_1 @ X2 @ X1)))),
% 15.68/15.86      inference('simplify', [status(thm)], ['20'])).
% 15.68/15.86  thf(t19_xboole_1, axiom,
% 15.68/15.86    (![A:$i,B:$i,C:$i]:
% 15.68/15.86     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 15.68/15.86       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 15.68/15.86  thf('24', plain,
% 15.68/15.86      (![X2 : $i, X3 : $i, X4 : $i]:
% 15.68/15.86         (~ (r1_tarski @ X2 @ X3)
% 15.68/15.86          | ~ (r1_tarski @ X2 @ X4)
% 15.68/15.86          | (r1_tarski @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 15.68/15.86      inference('cnf', [status(esa)], [t19_xboole_1])).
% 15.68/15.86  thf('25', plain,
% 15.68/15.86      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 15.68/15.86         (~ (v1_relat_1 @ X1)
% 15.68/15.86          | (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ 
% 15.68/15.86             (k3_xboole_0 @ (k9_relat_1 @ X1 @ X0) @ X3))
% 15.68/15.86          | ~ (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ X3))),
% 15.68/15.86      inference('sup-', [status(thm)], ['23', '24'])).
% 15.68/15.86  thf('26', plain,
% 15.68/15.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.68/15.86         (~ (v1_relat_1 @ X1)
% 15.68/15.86          | (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 15.68/15.86             (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ (k9_relat_1 @ X1 @ X0)))
% 15.68/15.86          | ~ (v1_relat_1 @ X1))),
% 15.68/15.86      inference('sup-', [status(thm)], ['22', '25'])).
% 15.68/15.86  thf('27', plain,
% 15.68/15.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.68/15.86         ((r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 15.68/15.86           (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ (k9_relat_1 @ X1 @ X0)))
% 15.68/15.86          | ~ (v1_relat_1 @ X1))),
% 15.68/15.86      inference('simplify', [status(thm)], ['26'])).
% 15.68/15.86  thf(t154_relat_1, conjecture,
% 15.68/15.86    (![A:$i,B:$i,C:$i]:
% 15.68/15.86     ( ( v1_relat_1 @ C ) =>
% 15.68/15.86       ( r1_tarski @
% 15.68/15.86         ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 15.68/15.86         ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 15.68/15.86  thf(zf_stmt_0, negated_conjecture,
% 15.68/15.86    (~( ![A:$i,B:$i,C:$i]:
% 15.68/15.86        ( ( v1_relat_1 @ C ) =>
% 15.68/15.86          ( r1_tarski @
% 15.68/15.86            ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 15.68/15.86            ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )),
% 15.68/15.86    inference('cnf.neg', [status(esa)], [t154_relat_1])).
% 15.68/15.86  thf('28', plain,
% 15.68/15.86      (~ (r1_tarski @ (k9_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 15.68/15.86          (k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ 
% 15.68/15.86           (k9_relat_1 @ sk_C @ sk_B)))),
% 15.68/15.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.68/15.86  thf('29', plain, (~ (v1_relat_1 @ sk_C)),
% 15.68/15.86      inference('sup-', [status(thm)], ['27', '28'])).
% 15.68/15.86  thf('30', plain, ((v1_relat_1 @ sk_C)),
% 15.68/15.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.68/15.86  thf('31', plain, ($false), inference('demod', [status(thm)], ['29', '30'])).
% 15.68/15.86  
% 15.68/15.86  % SZS output end Refutation
% 15.68/15.86  
% 15.68/15.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
