%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QfROoFW3Ua

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:28 EST 2020

% Result     : Theorem 6.83s
% Output     : Refutation 6.83s
% Verified   : 
% Statistics : Number of formulae       :   58 (  71 expanded)
%              Number of leaves         :   21 (  29 expanded)
%              Depth                    :   13
%              Number of atoms          :  514 ( 653 expanded)
%              Number of equality atoms :   14 (  20 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X33 @ X34 ) )
        = ( k9_relat_1 @ X33 @ X34 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ ( k4_xboole_0 @ X13 @ X14 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf(t31_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ ( k3_xboole_0 @ X10 @ X12 ) ) @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t31_xboole_1])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X7 @ X8 ) @ ( k3_xboole_0 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('4',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ ( k4_xboole_0 @ X13 @ X14 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t103_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k7_relat_1 @ C @ A ) ) ) ) )).

thf('8',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ X30 @ X31 )
      | ~ ( v1_relat_1 @ X32 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X32 @ X31 ) @ X30 )
        = ( k7_relat_1 @ X32 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t103_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X33 @ X34 ) )
        = ( k9_relat_1 @ X33 @ X34 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t99_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k2_relat_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X35: $i,X36: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X35 @ X36 ) ) @ ( k2_relat_1 @ X35 ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
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
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ ( k9_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ ( k9_relat_1 @ X2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['0','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X33 @ X34 ) )
        = ( k9_relat_1 @ X33 @ X34 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('21',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ X30 @ X31 )
      | ~ ( v1_relat_1 @ X32 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X32 @ X31 ) @ X30 )
        = ( k7_relat_1 @ X32 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t103_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
        = ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ ( k9_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ ( k9_relat_1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['19','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('28',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X4 @ X6 )
      | ( r1_tarski @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf(t154_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t154_relat_1])).

thf('32',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['33','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QfROoFW3Ua
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:39:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 6.83/7.02  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.83/7.02  % Solved by: fo/fo7.sh
% 6.83/7.02  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.83/7.02  % done 1405 iterations in 6.557s
% 6.83/7.02  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.83/7.02  % SZS output start Refutation
% 6.83/7.02  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 6.83/7.02  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 6.83/7.02  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.83/7.02  thf(sk_C_type, type, sk_C: $i).
% 6.83/7.02  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.83/7.02  thf(sk_B_type, type, sk_B: $i).
% 6.83/7.02  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 6.83/7.02  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 6.83/7.02  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 6.83/7.02  thf(sk_A_type, type, sk_A: $i).
% 6.83/7.02  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 6.83/7.02  thf(t148_relat_1, axiom,
% 6.83/7.02    (![A:$i,B:$i]:
% 6.83/7.02     ( ( v1_relat_1 @ B ) =>
% 6.83/7.02       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 6.83/7.02  thf('0', plain,
% 6.83/7.02      (![X33 : $i, X34 : $i]:
% 6.83/7.02         (((k2_relat_1 @ (k7_relat_1 @ X33 @ X34)) = (k9_relat_1 @ X33 @ X34))
% 6.83/7.02          | ~ (v1_relat_1 @ X33))),
% 6.83/7.02      inference('cnf', [status(esa)], [t148_relat_1])).
% 6.83/7.02  thf(t51_xboole_1, axiom,
% 6.83/7.02    (![A:$i,B:$i]:
% 6.83/7.02     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 6.83/7.02       ( A ) ))).
% 6.83/7.02  thf('1', plain,
% 6.83/7.02      (![X13 : $i, X14 : $i]:
% 6.83/7.02         ((k2_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ (k4_xboole_0 @ X13 @ X14))
% 6.83/7.02           = (X13))),
% 6.83/7.02      inference('cnf', [status(esa)], [t51_xboole_1])).
% 6.83/7.02  thf(t31_xboole_1, axiom,
% 6.83/7.02    (![A:$i,B:$i,C:$i]:
% 6.83/7.02     ( r1_tarski @
% 6.83/7.02       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 6.83/7.02       ( k2_xboole_0 @ B @ C ) ))).
% 6.83/7.02  thf('2', plain,
% 6.83/7.02      (![X10 : $i, X11 : $i, X12 : $i]:
% 6.83/7.02         (r1_tarski @ 
% 6.83/7.02          (k2_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ (k3_xboole_0 @ X10 @ X12)) @ 
% 6.83/7.02          (k2_xboole_0 @ X11 @ X12))),
% 6.83/7.02      inference('cnf', [status(esa)], [t31_xboole_1])).
% 6.83/7.02  thf(t23_xboole_1, axiom,
% 6.83/7.02    (![A:$i,B:$i,C:$i]:
% 6.83/7.02     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 6.83/7.02       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 6.83/7.02  thf('3', plain,
% 6.83/7.02      (![X7 : $i, X8 : $i, X9 : $i]:
% 6.83/7.02         ((k3_xboole_0 @ X7 @ (k2_xboole_0 @ X8 @ X9))
% 6.83/7.02           = (k2_xboole_0 @ (k3_xboole_0 @ X7 @ X8) @ (k3_xboole_0 @ X7 @ X9)))),
% 6.83/7.02      inference('cnf', [status(esa)], [t23_xboole_1])).
% 6.83/7.02  thf('4', plain,
% 6.83/7.02      (![X10 : $i, X11 : $i, X12 : $i]:
% 6.83/7.02         (r1_tarski @ (k3_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)) @ 
% 6.83/7.02          (k2_xboole_0 @ X11 @ X12))),
% 6.83/7.02      inference('demod', [status(thm)], ['2', '3'])).
% 6.83/7.02  thf('5', plain,
% 6.83/7.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.83/7.02         (r1_tarski @ (k3_xboole_0 @ X2 @ X0) @ 
% 6.83/7.02          (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1)))),
% 6.83/7.02      inference('sup+', [status(thm)], ['1', '4'])).
% 6.83/7.02  thf('6', plain,
% 6.83/7.02      (![X13 : $i, X14 : $i]:
% 6.83/7.02         ((k2_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ (k4_xboole_0 @ X13 @ X14))
% 6.83/7.02           = (X13))),
% 6.83/7.02      inference('cnf', [status(esa)], [t51_xboole_1])).
% 6.83/7.02  thf('7', plain,
% 6.83/7.02      (![X0 : $i, X2 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X0) @ X0)),
% 6.83/7.02      inference('demod', [status(thm)], ['5', '6'])).
% 6.83/7.02  thf(t103_relat_1, axiom,
% 6.83/7.02    (![A:$i,B:$i,C:$i]:
% 6.83/7.02     ( ( v1_relat_1 @ C ) =>
% 6.83/7.02       ( ( r1_tarski @ A @ B ) =>
% 6.83/7.02         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k7_relat_1 @ C @ A ) ) ) ))).
% 6.83/7.02  thf('8', plain,
% 6.83/7.02      (![X30 : $i, X31 : $i, X32 : $i]:
% 6.83/7.02         (~ (r1_tarski @ X30 @ X31)
% 6.83/7.02          | ~ (v1_relat_1 @ X32)
% 6.83/7.02          | ((k7_relat_1 @ (k7_relat_1 @ X32 @ X31) @ X30)
% 6.83/7.02              = (k7_relat_1 @ X32 @ X30)))),
% 6.83/7.02      inference('cnf', [status(esa)], [t103_relat_1])).
% 6.83/7.02  thf('9', plain,
% 6.83/7.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.83/7.02         (((k7_relat_1 @ (k7_relat_1 @ X2 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 6.83/7.02            = (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 6.83/7.02          | ~ (v1_relat_1 @ X2))),
% 6.83/7.02      inference('sup-', [status(thm)], ['7', '8'])).
% 6.83/7.02  thf('10', plain,
% 6.83/7.02      (![X33 : $i, X34 : $i]:
% 6.83/7.02         (((k2_relat_1 @ (k7_relat_1 @ X33 @ X34)) = (k9_relat_1 @ X33 @ X34))
% 6.83/7.02          | ~ (v1_relat_1 @ X33))),
% 6.83/7.02      inference('cnf', [status(esa)], [t148_relat_1])).
% 6.83/7.02  thf(t99_relat_1, axiom,
% 6.83/7.02    (![A:$i,B:$i]:
% 6.83/7.02     ( ( v1_relat_1 @ B ) =>
% 6.83/7.02       ( r1_tarski @
% 6.83/7.02         ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k2_relat_1 @ B ) ) ))).
% 6.83/7.02  thf('11', plain,
% 6.83/7.02      (![X35 : $i, X36 : $i]:
% 6.83/7.02         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X35 @ X36)) @ 
% 6.83/7.02           (k2_relat_1 @ X35))
% 6.83/7.02          | ~ (v1_relat_1 @ X35))),
% 6.83/7.02      inference('cnf', [status(esa)], [t99_relat_1])).
% 6.83/7.02  thf('12', plain,
% 6.83/7.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.83/7.02         ((r1_tarski @ 
% 6.83/7.02           (k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)) @ 
% 6.83/7.02           (k9_relat_1 @ X1 @ X0))
% 6.83/7.02          | ~ (v1_relat_1 @ X1)
% 6.83/7.02          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 6.83/7.02      inference('sup+', [status(thm)], ['10', '11'])).
% 6.83/7.02  thf(dt_k7_relat_1, axiom,
% 6.83/7.02    (![A:$i,B:$i]:
% 6.83/7.02     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 6.83/7.02  thf('13', plain,
% 6.83/7.02      (![X28 : $i, X29 : $i]:
% 6.83/7.02         (~ (v1_relat_1 @ X28) | (v1_relat_1 @ (k7_relat_1 @ X28 @ X29)))),
% 6.83/7.02      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 6.83/7.02  thf('14', plain,
% 6.83/7.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.83/7.02         (~ (v1_relat_1 @ X1)
% 6.83/7.02          | (r1_tarski @ 
% 6.83/7.02             (k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)) @ 
% 6.83/7.02             (k9_relat_1 @ X1 @ X0)))),
% 6.83/7.02      inference('clc', [status(thm)], ['12', '13'])).
% 6.83/7.02  thf('15', plain,
% 6.83/7.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.83/7.02         ((r1_tarski @ 
% 6.83/7.02           (k2_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))) @ 
% 6.83/7.02           (k9_relat_1 @ X2 @ X0))
% 6.83/7.02          | ~ (v1_relat_1 @ X2)
% 6.83/7.02          | ~ (v1_relat_1 @ X2))),
% 6.83/7.02      inference('sup+', [status(thm)], ['9', '14'])).
% 6.83/7.02  thf('16', plain,
% 6.83/7.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.83/7.02         (~ (v1_relat_1 @ X2)
% 6.83/7.02          | (r1_tarski @ 
% 6.83/7.02             (k2_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))) @ 
% 6.83/7.02             (k9_relat_1 @ X2 @ X0)))),
% 6.83/7.02      inference('simplify', [status(thm)], ['15'])).
% 6.83/7.02  thf('17', plain,
% 6.83/7.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.83/7.02         ((r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 6.83/7.02           (k9_relat_1 @ X2 @ X0))
% 6.83/7.02          | ~ (v1_relat_1 @ X2)
% 6.83/7.02          | ~ (v1_relat_1 @ X2))),
% 6.83/7.02      inference('sup+', [status(thm)], ['0', '16'])).
% 6.83/7.02  thf('18', plain,
% 6.83/7.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.83/7.02         (~ (v1_relat_1 @ X2)
% 6.83/7.02          | (r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 6.83/7.02             (k9_relat_1 @ X2 @ X0)))),
% 6.83/7.02      inference('simplify', [status(thm)], ['17'])).
% 6.83/7.02  thf('19', plain,
% 6.83/7.02      (![X33 : $i, X34 : $i]:
% 6.83/7.02         (((k2_relat_1 @ (k7_relat_1 @ X33 @ X34)) = (k9_relat_1 @ X33 @ X34))
% 6.83/7.02          | ~ (v1_relat_1 @ X33))),
% 6.83/7.02      inference('cnf', [status(esa)], [t148_relat_1])).
% 6.83/7.02  thf(t17_xboole_1, axiom,
% 6.83/7.02    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 6.83/7.02  thf('20', plain,
% 6.83/7.02      (![X2 : $i, X3 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ X2)),
% 6.83/7.02      inference('cnf', [status(esa)], [t17_xboole_1])).
% 6.83/7.02  thf('21', plain,
% 6.83/7.02      (![X30 : $i, X31 : $i, X32 : $i]:
% 6.83/7.02         (~ (r1_tarski @ X30 @ X31)
% 6.83/7.02          | ~ (v1_relat_1 @ X32)
% 6.83/7.02          | ((k7_relat_1 @ (k7_relat_1 @ X32 @ X31) @ X30)
% 6.83/7.02              = (k7_relat_1 @ X32 @ X30)))),
% 6.83/7.02      inference('cnf', [status(esa)], [t103_relat_1])).
% 6.83/7.02  thf('22', plain,
% 6.83/7.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.83/7.02         (((k7_relat_1 @ (k7_relat_1 @ X2 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 6.83/7.02            = (k7_relat_1 @ X2 @ (k3_xboole_0 @ X0 @ X1)))
% 6.83/7.02          | ~ (v1_relat_1 @ X2))),
% 6.83/7.02      inference('sup-', [status(thm)], ['20', '21'])).
% 6.83/7.02  thf('23', plain,
% 6.83/7.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.83/7.02         (~ (v1_relat_1 @ X1)
% 6.83/7.02          | (r1_tarski @ 
% 6.83/7.02             (k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)) @ 
% 6.83/7.02             (k9_relat_1 @ X1 @ X0)))),
% 6.83/7.02      inference('clc', [status(thm)], ['12', '13'])).
% 6.83/7.02  thf('24', plain,
% 6.83/7.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.83/7.02         ((r1_tarski @ 
% 6.83/7.02           (k2_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))) @ 
% 6.83/7.02           (k9_relat_1 @ X2 @ X1))
% 6.83/7.02          | ~ (v1_relat_1 @ X2)
% 6.83/7.02          | ~ (v1_relat_1 @ X2))),
% 6.83/7.02      inference('sup+', [status(thm)], ['22', '23'])).
% 6.83/7.02  thf('25', plain,
% 6.83/7.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.83/7.02         (~ (v1_relat_1 @ X2)
% 6.83/7.02          | (r1_tarski @ 
% 6.83/7.02             (k2_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))) @ 
% 6.83/7.02             (k9_relat_1 @ X2 @ X1)))),
% 6.83/7.02      inference('simplify', [status(thm)], ['24'])).
% 6.83/7.02  thf('26', plain,
% 6.83/7.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.83/7.02         ((r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 6.83/7.02           (k9_relat_1 @ X2 @ X1))
% 6.83/7.02          | ~ (v1_relat_1 @ X2)
% 6.83/7.02          | ~ (v1_relat_1 @ X2))),
% 6.83/7.02      inference('sup+', [status(thm)], ['19', '25'])).
% 6.83/7.02  thf('27', plain,
% 6.83/7.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.83/7.02         (~ (v1_relat_1 @ X2)
% 6.83/7.02          | (r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 6.83/7.02             (k9_relat_1 @ X2 @ X1)))),
% 6.83/7.02      inference('simplify', [status(thm)], ['26'])).
% 6.83/7.02  thf(t19_xboole_1, axiom,
% 6.83/7.02    (![A:$i,B:$i,C:$i]:
% 6.83/7.02     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 6.83/7.02       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 6.83/7.02  thf('28', plain,
% 6.83/7.02      (![X4 : $i, X5 : $i, X6 : $i]:
% 6.83/7.02         (~ (r1_tarski @ X4 @ X5)
% 6.83/7.02          | ~ (r1_tarski @ X4 @ X6)
% 6.83/7.02          | (r1_tarski @ X4 @ (k3_xboole_0 @ X5 @ X6)))),
% 6.83/7.02      inference('cnf', [status(esa)], [t19_xboole_1])).
% 6.83/7.02  thf('29', plain,
% 6.83/7.02      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.83/7.02         (~ (v1_relat_1 @ X1)
% 6.83/7.02          | (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ 
% 6.83/7.02             (k3_xboole_0 @ (k9_relat_1 @ X1 @ X0) @ X3))
% 6.83/7.02          | ~ (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ X3))),
% 6.83/7.02      inference('sup-', [status(thm)], ['27', '28'])).
% 6.83/7.02  thf('30', plain,
% 6.83/7.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.83/7.02         (~ (v1_relat_1 @ X1)
% 6.83/7.02          | (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 6.83/7.02             (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ (k9_relat_1 @ X1 @ X0)))
% 6.83/7.02          | ~ (v1_relat_1 @ X1))),
% 6.83/7.02      inference('sup-', [status(thm)], ['18', '29'])).
% 6.83/7.02  thf('31', plain,
% 6.83/7.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.83/7.02         ((r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 6.83/7.02           (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ (k9_relat_1 @ X1 @ X0)))
% 6.83/7.02          | ~ (v1_relat_1 @ X1))),
% 6.83/7.02      inference('simplify', [status(thm)], ['30'])).
% 6.83/7.02  thf(t154_relat_1, conjecture,
% 6.83/7.02    (![A:$i,B:$i,C:$i]:
% 6.83/7.02     ( ( v1_relat_1 @ C ) =>
% 6.83/7.02       ( r1_tarski @
% 6.83/7.02         ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 6.83/7.02         ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 6.83/7.02  thf(zf_stmt_0, negated_conjecture,
% 6.83/7.02    (~( ![A:$i,B:$i,C:$i]:
% 6.83/7.02        ( ( v1_relat_1 @ C ) =>
% 6.83/7.02          ( r1_tarski @
% 6.83/7.02            ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 6.83/7.02            ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )),
% 6.83/7.02    inference('cnf.neg', [status(esa)], [t154_relat_1])).
% 6.83/7.02  thf('32', plain,
% 6.83/7.02      (~ (r1_tarski @ (k9_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 6.83/7.02          (k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ 
% 6.83/7.02           (k9_relat_1 @ sk_C @ sk_B)))),
% 6.83/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.83/7.02  thf('33', plain, (~ (v1_relat_1 @ sk_C)),
% 6.83/7.02      inference('sup-', [status(thm)], ['31', '32'])).
% 6.83/7.02  thf('34', plain, ((v1_relat_1 @ sk_C)),
% 6.83/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.83/7.02  thf('35', plain, ($false), inference('demod', [status(thm)], ['33', '34'])).
% 6.83/7.02  
% 6.83/7.02  % SZS output end Refutation
% 6.83/7.02  
% 6.87/7.03  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
