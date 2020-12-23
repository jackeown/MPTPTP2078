%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YyIKaUjdfc

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:29 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   56 (  64 expanded)
%              Number of leaves         :   24 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :  379 ( 469 expanded)
%              Number of equality atoms :   36 (  45 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(t27_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
        = ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ) )).

thf('0',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X24 @ X26 ) @ X25 )
        = ( k2_wellord1 @ ( k2_wellord1 @ X24 @ X25 ) @ X26 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t27_wellord1])).

thf(t26_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
        = ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X21 @ X22 ) @ X23 )
        = ( k2_wellord1 @ X21 @ ( k3_xboole_0 @ X22 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t26_wellord1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('3',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X21 @ X22 ) @ X23 )
        = ( k2_wellord1 @ X21 @ ( k1_setfam_1 @ ( k2_tarski @ X22 @ X23 ) ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X2 @ X1 ) @ X0 )
        = ( k2_wellord1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['0','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k2_wellord1 @ ( k2_wellord1 @ X2 @ X1 ) @ X0 )
        = ( k2_wellord1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t29_wellord1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A )
          = ( k2_wellord1 @ C @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A )
            = ( k2_wellord1 @ C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_wellord1])).

thf('6',plain,(
    ( k2_wellord1 @ ( k2_wellord1 @ sk_C @ sk_B ) @ sk_A )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( ( k2_wellord1 @ sk_C @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) )
     != ( k2_wellord1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ( k2_wellord1 @ sk_C @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('11',plain,(
    ! [X11: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('12',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X15 ) @ X16 )
      | ( ( k7_relat_1 @ X15 @ X16 )
        = X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('14',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
    = ( k6_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X20 ) @ ( k6_relat_1 @ X19 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('18',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('19',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X20 ) @ ( k6_relat_1 @ X19 ) )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k7_relat_1 @ X14 @ X13 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X13 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X11: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    = ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['16','25'])).

thf('27',plain,(
    ! [X11: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('28',plain,
    ( sk_A
    = ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ( k2_wellord1 @ sk_C @ sk_A )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['9','28'])).

thf('30',plain,(
    $false ),
    inference(simplify,[status(thm)],['29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YyIKaUjdfc
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:26:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 42 iterations in 0.028s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.48  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.48  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.19/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.48  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.19/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.48  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.19/0.48  thf(t27_wellord1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( v1_relat_1 @ C ) =>
% 0.19/0.48       ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 0.19/0.48         ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ))).
% 0.19/0.48  thf('0', plain,
% 0.19/0.48      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.19/0.48         (((k2_wellord1 @ (k2_wellord1 @ X24 @ X26) @ X25)
% 0.19/0.48            = (k2_wellord1 @ (k2_wellord1 @ X24 @ X25) @ X26))
% 0.19/0.48          | ~ (v1_relat_1 @ X24))),
% 0.19/0.48      inference('cnf', [status(esa)], [t27_wellord1])).
% 0.19/0.48  thf(t26_wellord1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( v1_relat_1 @ C ) =>
% 0.19/0.48       ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 0.19/0.48         ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.19/0.48  thf('1', plain,
% 0.19/0.48      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.19/0.48         (((k2_wellord1 @ (k2_wellord1 @ X21 @ X22) @ X23)
% 0.19/0.48            = (k2_wellord1 @ X21 @ (k3_xboole_0 @ X22 @ X23)))
% 0.19/0.48          | ~ (v1_relat_1 @ X21))),
% 0.19/0.48      inference('cnf', [status(esa)], [t26_wellord1])).
% 0.19/0.48  thf(t12_setfam_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.19/0.48  thf('2', plain,
% 0.19/0.48      (![X9 : $i, X10 : $i]:
% 0.19/0.48         ((k1_setfam_1 @ (k2_tarski @ X9 @ X10)) = (k3_xboole_0 @ X9 @ X10))),
% 0.19/0.48      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.19/0.48         (((k2_wellord1 @ (k2_wellord1 @ X21 @ X22) @ X23)
% 0.19/0.48            = (k2_wellord1 @ X21 @ (k1_setfam_1 @ (k2_tarski @ X22 @ X23))))
% 0.19/0.48          | ~ (v1_relat_1 @ X21))),
% 0.19/0.48      inference('demod', [status(thm)], ['1', '2'])).
% 0.19/0.48  thf('4', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.48         (((k2_wellord1 @ (k2_wellord1 @ X2 @ X1) @ X0)
% 0.19/0.48            = (k2_wellord1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))
% 0.19/0.48          | ~ (v1_relat_1 @ X2)
% 0.19/0.48          | ~ (v1_relat_1 @ X2))),
% 0.19/0.48      inference('sup+', [status(thm)], ['0', '3'])).
% 0.19/0.48  thf('5', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.48         (~ (v1_relat_1 @ X2)
% 0.19/0.48          | ((k2_wellord1 @ (k2_wellord1 @ X2 @ X1) @ X0)
% 0.19/0.48              = (k2_wellord1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))))),
% 0.19/0.48      inference('simplify', [status(thm)], ['4'])).
% 0.19/0.48  thf(t29_wellord1, conjecture,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( v1_relat_1 @ C ) =>
% 0.19/0.48       ( ( r1_tarski @ A @ B ) =>
% 0.19/0.48         ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 0.19/0.48           ( k2_wellord1 @ C @ A ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.48        ( ( v1_relat_1 @ C ) =>
% 0.19/0.48          ( ( r1_tarski @ A @ B ) =>
% 0.19/0.48            ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 0.19/0.48              ( k2_wellord1 @ C @ A ) ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t29_wellord1])).
% 0.19/0.48  thf('6', plain,
% 0.19/0.48      (((k2_wellord1 @ (k2_wellord1 @ sk_C @ sk_B) @ sk_A)
% 0.19/0.48         != (k2_wellord1 @ sk_C @ sk_A))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('7', plain,
% 0.19/0.48      ((((k2_wellord1 @ sk_C @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B)))
% 0.19/0.48          != (k2_wellord1 @ sk_C @ sk_A))
% 0.19/0.48        | ~ (v1_relat_1 @ sk_C))),
% 0.19/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.48  thf('8', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('9', plain,
% 0.19/0.48      (((k2_wellord1 @ sk_C @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B)))
% 0.19/0.48         != (k2_wellord1 @ sk_C @ sk_A))),
% 0.19/0.48      inference('demod', [status(thm)], ['7', '8'])).
% 0.19/0.48  thf('10', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t71_relat_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.19/0.48       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.19/0.48  thf('11', plain, (![X11 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 0.19/0.48      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.48  thf(t97_relat_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( v1_relat_1 @ B ) =>
% 0.19/0.48       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.19/0.48         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.19/0.48  thf('12', plain,
% 0.19/0.48      (![X15 : $i, X16 : $i]:
% 0.19/0.48         (~ (r1_tarski @ (k1_relat_1 @ X15) @ X16)
% 0.19/0.48          | ((k7_relat_1 @ X15 @ X16) = (X15))
% 0.19/0.48          | ~ (v1_relat_1 @ X15))),
% 0.19/0.48      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.19/0.48  thf('13', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (~ (r1_tarski @ X0 @ X1)
% 0.19/0.48          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.19/0.48          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.48  thf(fc3_funct_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.19/0.48       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.19/0.48  thf('14', plain, (![X17 : $i]: (v1_relat_1 @ (k6_relat_1 @ X17))),
% 0.19/0.48      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.48  thf('15', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (~ (r1_tarski @ X0 @ X1)
% 0.19/0.48          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.19/0.48      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.48  thf('16', plain,
% 0.19/0.48      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (k6_relat_1 @ sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['10', '15'])).
% 0.19/0.48  thf(t43_funct_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.19/0.48       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.48  thf('17', plain,
% 0.19/0.48      (![X19 : $i, X20 : $i]:
% 0.19/0.48         ((k5_relat_1 @ (k6_relat_1 @ X20) @ (k6_relat_1 @ X19))
% 0.19/0.48           = (k6_relat_1 @ (k3_xboole_0 @ X19 @ X20)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.19/0.48  thf('18', plain,
% 0.19/0.48      (![X9 : $i, X10 : $i]:
% 0.19/0.48         ((k1_setfam_1 @ (k2_tarski @ X9 @ X10)) = (k3_xboole_0 @ X9 @ X10))),
% 0.19/0.48      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.19/0.48  thf('19', plain,
% 0.19/0.48      (![X19 : $i, X20 : $i]:
% 0.19/0.48         ((k5_relat_1 @ (k6_relat_1 @ X20) @ (k6_relat_1 @ X19))
% 0.19/0.48           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X19 @ X20))))),
% 0.19/0.48      inference('demod', [status(thm)], ['17', '18'])).
% 0.19/0.48  thf(t94_relat_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( v1_relat_1 @ B ) =>
% 0.19/0.48       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.19/0.48  thf('20', plain,
% 0.19/0.48      (![X13 : $i, X14 : $i]:
% 0.19/0.48         (((k7_relat_1 @ X14 @ X13) = (k5_relat_1 @ (k6_relat_1 @ X13) @ X14))
% 0.19/0.48          | ~ (v1_relat_1 @ X14))),
% 0.19/0.48      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.19/0.48  thf('21', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.19/0.48            = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))
% 0.19/0.48          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.19/0.48      inference('sup+', [status(thm)], ['19', '20'])).
% 0.19/0.48  thf('22', plain, (![X17 : $i]: (v1_relat_1 @ (k6_relat_1 @ X17))),
% 0.19/0.48      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.48  thf('23', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.19/0.48           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.19/0.48      inference('demod', [status(thm)], ['21', '22'])).
% 0.19/0.48  thf('24', plain, (![X11 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 0.19/0.48      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.48  thf('25', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.19/0.48           = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 0.19/0.48      inference('sup+', [status(thm)], ['23', '24'])).
% 0.19/0.48  thf('26', plain,
% 0.19/0.48      (((k1_relat_1 @ (k6_relat_1 @ sk_A))
% 0.19/0.48         = (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.19/0.48      inference('sup+', [status(thm)], ['16', '25'])).
% 0.19/0.48  thf('27', plain, (![X11 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 0.19/0.48      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.48  thf('28', plain, (((sk_A) = (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.19/0.48      inference('demod', [status(thm)], ['26', '27'])).
% 0.19/0.48  thf('29', plain,
% 0.19/0.48      (((k2_wellord1 @ sk_C @ sk_A) != (k2_wellord1 @ sk_C @ sk_A))),
% 0.19/0.48      inference('demod', [status(thm)], ['9', '28'])).
% 0.19/0.48  thf('30', plain, ($false), inference('simplify', [status(thm)], ['29'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
