%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pJWkiACTJa

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   49 (  58 expanded)
%              Number of leaves         :   19 (  27 expanded)
%              Depth                    :   12
%              Number of atoms          :  363 ( 447 expanded)
%              Number of equality atoms :   30 (  36 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k8_relat_1 @ X8 @ X7 )
        = ( k5_relat_1 @ X7 @ ( k6_relat_1 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t159_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k9_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k9_relat_1 @ C @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k9_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) @ X11 )
        = ( k9_relat_1 @ X9 @ ( k9_relat_1 @ X10 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t159_relat_1])).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k8_relat_1 @ X8 @ X7 )
        = ( k5_relat_1 @ X7 @ ( k6_relat_1 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('3',plain,(
    ! [X15: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) )
        = ( k9_relat_1 @ X12 @ ( k2_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['2','7'])).

thf('9',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k8_relat_1 @ X8 @ X7 )
        = ( k5_relat_1 @ X7 @ ( k6_relat_1 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X19 ) @ ( k6_relat_1 @ X18 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X15: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('17',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['8','15','16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ ( k9_relat_1 @ X2 @ X0 ) )
        = ( k9_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','18'])).

thf('20',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ ( k9_relat_1 @ X2 @ X0 ) )
        = ( k9_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ ( k9_relat_1 @ X0 @ X2 ) )
        = ( k9_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ X1 @ ( k9_relat_1 @ X0 @ X2 ) )
        = ( k9_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(t126_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k9_relat_1 @ ( k8_relat_1 @ A @ C ) @ B )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( k9_relat_1 @ ( k8_relat_1 @ A @ C ) @ B )
          = ( k3_xboole_0 @ A @ ( k9_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t126_funct_1])).

thf('24',plain,(
    ( k9_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C ) @ sk_B )
 != ( k3_xboole_0 @ sk_A @ ( k9_relat_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ( k9_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C ) @ sk_B )
     != ( k9_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C ) @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ( k9_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C ) @ sk_B )
 != ( k9_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    $false ),
    inference(simplify,[status(thm)],['27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pJWkiACTJa
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:40:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 56 iterations in 0.051s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.51  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.51  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.51  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.21/0.51  thf(t123_relat_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ B ) =>
% 0.21/0.51       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i]:
% 0.21/0.51         (((k8_relat_1 @ X8 @ X7) = (k5_relat_1 @ X7 @ (k6_relat_1 @ X8)))
% 0.21/0.51          | ~ (v1_relat_1 @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.21/0.51  thf(t159_relat_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ B ) =>
% 0.21/0.51       ( ![C:$i]:
% 0.21/0.51         ( ( v1_relat_1 @ C ) =>
% 0.21/0.51           ( ( k9_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.21/0.51             ( k9_relat_1 @ C @ ( k9_relat_1 @ B @ A ) ) ) ) ) ))).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X9)
% 0.21/0.51          | ((k9_relat_1 @ (k5_relat_1 @ X10 @ X9) @ X11)
% 0.21/0.51              = (k9_relat_1 @ X9 @ (k9_relat_1 @ X10 @ X11)))
% 0.21/0.51          | ~ (v1_relat_1 @ X10))),
% 0.21/0.51      inference('cnf', [status(esa)], [t159_relat_1])).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i]:
% 0.21/0.51         (((k8_relat_1 @ X8 @ X7) = (k5_relat_1 @ X7 @ (k6_relat_1 @ X8)))
% 0.21/0.51          | ~ (v1_relat_1 @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.21/0.51  thf(t71_relat_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.21/0.51       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.51  thf('3', plain, (![X15 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X15)) = (X15))),
% 0.21/0.51      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.51  thf(t160_relat_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( v1_relat_1 @ B ) =>
% 0.21/0.51           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.21/0.51             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (![X12 : $i, X13 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X12)
% 0.21/0.51          | ((k2_relat_1 @ (k5_relat_1 @ X13 @ X12))
% 0.21/0.51              = (k9_relat_1 @ X12 @ (k2_relat_1 @ X13)))
% 0.21/0.51          | ~ (v1_relat_1 @ X13))),
% 0.21/0.51      inference('cnf', [status(esa)], [t160_relat_1])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.21/0.51            = (k9_relat_1 @ X1 @ X0))
% 0.21/0.51          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.51          | ~ (v1_relat_1 @ X1))),
% 0.21/0.51      inference('sup+', [status(thm)], ['3', '4'])).
% 0.21/0.51  thf(fc3_funct_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.21/0.51       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.21/0.51  thf('6', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.21/0.51            = (k9_relat_1 @ X1 @ X0))
% 0.21/0.51          | ~ (v1_relat_1 @ X1))),
% 0.21/0.51      inference('demod', [status(thm)], ['5', '6'])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.21/0.51            = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.21/0.51          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.51          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['2', '7'])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i]:
% 0.21/0.51         (((k8_relat_1 @ X8 @ X7) = (k5_relat_1 @ X7 @ (k6_relat_1 @ X8)))
% 0.21/0.51          | ~ (v1_relat_1 @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.21/0.51  thf(t43_funct_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.21/0.51       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X18 : $i, X19 : $i]:
% 0.21/0.51         ((k5_relat_1 @ (k6_relat_1 @ X19) @ (k6_relat_1 @ X18))
% 0.21/0.51           = (k6_relat_1 @ (k3_xboole_0 @ X18 @ X19)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.21/0.51            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.21/0.51          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.51  thf('12', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.21/0.51           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.51      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf('14', plain, (![X15 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X15)) = (X15))),
% 0.21/0.51      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.21/0.51           = (k3_xboole_0 @ X1 @ X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf('16', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.51  thf('17', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((k3_xboole_0 @ X1 @ X0) = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['8', '15', '16', '17'])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (((k3_xboole_0 @ X1 @ (k9_relat_1 @ X2 @ X0))
% 0.21/0.51            = (k9_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0))
% 0.21/0.51          | ~ (v1_relat_1 @ X2)
% 0.21/0.51          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['1', '18'])).
% 0.21/0.51  thf('20', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (((k3_xboole_0 @ X1 @ (k9_relat_1 @ X2 @ X0))
% 0.21/0.51            = (k9_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0))
% 0.21/0.51          | ~ (v1_relat_1 @ X2))),
% 0.21/0.51      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (((k3_xboole_0 @ X1 @ (k9_relat_1 @ X0 @ X2))
% 0.21/0.51            = (k9_relat_1 @ (k8_relat_1 @ X1 @ X0) @ X2))
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['0', '21'])).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X0)
% 0.21/0.51          | ((k3_xboole_0 @ X1 @ (k9_relat_1 @ X0 @ X2))
% 0.21/0.51              = (k9_relat_1 @ (k8_relat_1 @ X1 @ X0) @ X2)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.51  thf(t126_funct_1, conjecture,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.51       ( ( k9_relat_1 @ ( k8_relat_1 @ A @ C ) @ B ) =
% 0.21/0.51         ( k3_xboole_0 @ A @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.51        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.51          ( ( k9_relat_1 @ ( k8_relat_1 @ A @ C ) @ B ) =
% 0.21/0.51            ( k3_xboole_0 @ A @ ( k9_relat_1 @ C @ B ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t126_funct_1])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (((k9_relat_1 @ (k8_relat_1 @ sk_A @ sk_C) @ sk_B)
% 0.21/0.51         != (k3_xboole_0 @ sk_A @ (k9_relat_1 @ sk_C @ sk_B)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      ((((k9_relat_1 @ (k8_relat_1 @ sk_A @ sk_C) @ sk_B)
% 0.21/0.51          != (k9_relat_1 @ (k8_relat_1 @ sk_A @ sk_C) @ sk_B))
% 0.21/0.51        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.51  thf('26', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (((k9_relat_1 @ (k8_relat_1 @ sk_A @ sk_C) @ sk_B)
% 0.21/0.51         != (k9_relat_1 @ (k8_relat_1 @ sk_A @ sk_C) @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.51  thf('28', plain, ($false), inference('simplify', [status(thm)], ['27'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
