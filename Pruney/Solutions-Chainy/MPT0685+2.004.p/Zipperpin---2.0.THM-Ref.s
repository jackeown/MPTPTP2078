%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BKCuF2wy90

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:08 EST 2020

% Result     : Theorem 0.66s
% Output     : Refutation 0.66s
% Verified   : 
% Statistics : Number of formulae       :   52 (  61 expanded)
%              Number of leaves         :   20 (  28 expanded)
%              Depth                    :   13
%              Number of atoms          :  382 ( 462 expanded)
%              Number of equality atoms :   33 (  39 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k7_relat_1 @ X19 @ X18 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X18 ) @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t181_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) @ X13 )
        = ( k10_relat_1 @ X12 @ ( k10_relat_1 @ X11 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k7_relat_1 @ X19 @ X18 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X18 ) @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('3',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) )
        = ( k10_relat_1 @ X15 @ ( k1_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','7'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('10',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k7_relat_1 @ X19 @ X18 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X18 ) @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X23 ) @ ( k6_relat_1 @ X22 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('19',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['8','17','18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','20'])).

thf('22',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf(t139_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t139_funct_1])).

thf('26',plain,(
    ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B )
 != ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B )
     != ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    $false ),
    inference(simplify,[status(thm)],['29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BKCuF2wy90
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:03:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.66/0.84  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.66/0.84  % Solved by: fo/fo7.sh
% 0.66/0.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.66/0.84  % done 395 iterations in 0.383s
% 0.66/0.84  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.66/0.84  % SZS output start Refutation
% 0.66/0.84  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.66/0.84  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.66/0.84  thf(sk_B_type, type, sk_B: $i).
% 0.66/0.84  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.66/0.84  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.66/0.84  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.66/0.84  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.66/0.84  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.66/0.84  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.66/0.84  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.66/0.84  thf(sk_A_type, type, sk_A: $i).
% 0.66/0.84  thf(sk_C_type, type, sk_C: $i).
% 0.66/0.84  thf(t94_relat_1, axiom,
% 0.66/0.84    (![A:$i,B:$i]:
% 0.66/0.84     ( ( v1_relat_1 @ B ) =>
% 0.66/0.84       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.66/0.84  thf('0', plain,
% 0.66/0.84      (![X18 : $i, X19 : $i]:
% 0.66/0.84         (((k7_relat_1 @ X19 @ X18) = (k5_relat_1 @ (k6_relat_1 @ X18) @ X19))
% 0.66/0.84          | ~ (v1_relat_1 @ X19))),
% 0.66/0.84      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.66/0.84  thf(t181_relat_1, axiom,
% 0.66/0.84    (![A:$i,B:$i]:
% 0.66/0.84     ( ( v1_relat_1 @ B ) =>
% 0.66/0.84       ( ![C:$i]:
% 0.66/0.84         ( ( v1_relat_1 @ C ) =>
% 0.66/0.84           ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.66/0.84             ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.66/0.84  thf('1', plain,
% 0.66/0.84      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.66/0.84         (~ (v1_relat_1 @ X11)
% 0.66/0.84          | ((k10_relat_1 @ (k5_relat_1 @ X12 @ X11) @ X13)
% 0.66/0.84              = (k10_relat_1 @ X12 @ (k10_relat_1 @ X11 @ X13)))
% 0.66/0.84          | ~ (v1_relat_1 @ X12))),
% 0.66/0.84      inference('cnf', [status(esa)], [t181_relat_1])).
% 0.66/0.84  thf('2', plain,
% 0.66/0.84      (![X18 : $i, X19 : $i]:
% 0.66/0.84         (((k7_relat_1 @ X19 @ X18) = (k5_relat_1 @ (k6_relat_1 @ X18) @ X19))
% 0.66/0.84          | ~ (v1_relat_1 @ X19))),
% 0.66/0.84      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.66/0.84  thf(t71_relat_1, axiom,
% 0.66/0.84    (![A:$i]:
% 0.66/0.84     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.66/0.84       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.66/0.84  thf('3', plain, (![X16 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 0.66/0.84      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.66/0.84  thf(t182_relat_1, axiom,
% 0.66/0.84    (![A:$i]:
% 0.66/0.84     ( ( v1_relat_1 @ A ) =>
% 0.66/0.84       ( ![B:$i]:
% 0.66/0.84         ( ( v1_relat_1 @ B ) =>
% 0.66/0.84           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.66/0.84             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.66/0.84  thf('4', plain,
% 0.66/0.84      (![X14 : $i, X15 : $i]:
% 0.66/0.84         (~ (v1_relat_1 @ X14)
% 0.66/0.84          | ((k1_relat_1 @ (k5_relat_1 @ X15 @ X14))
% 0.66/0.84              = (k10_relat_1 @ X15 @ (k1_relat_1 @ X14)))
% 0.66/0.84          | ~ (v1_relat_1 @ X15))),
% 0.66/0.84      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.66/0.84  thf('5', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.66/0.84            = (k10_relat_1 @ X1 @ X0))
% 0.66/0.84          | ~ (v1_relat_1 @ X1)
% 0.66/0.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['3', '4'])).
% 0.66/0.84  thf(fc3_funct_1, axiom,
% 0.66/0.84    (![A:$i]:
% 0.66/0.84     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.66/0.84       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.66/0.84  thf('6', plain, (![X20 : $i]: (v1_relat_1 @ (k6_relat_1 @ X20))),
% 0.66/0.84      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.66/0.84  thf('7', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.66/0.84            = (k10_relat_1 @ X1 @ X0))
% 0.66/0.84          | ~ (v1_relat_1 @ X1))),
% 0.66/0.84      inference('demod', [status(thm)], ['5', '6'])).
% 0.66/0.84  thf('8', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.66/0.84            = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.66/0.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.66/0.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['2', '7'])).
% 0.66/0.84  thf(commutativity_k3_xboole_0, axiom,
% 0.66/0.84    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.66/0.84  thf('9', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.66/0.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.66/0.84  thf('10', plain,
% 0.66/0.84      (![X18 : $i, X19 : $i]:
% 0.66/0.84         (((k7_relat_1 @ X19 @ X18) = (k5_relat_1 @ (k6_relat_1 @ X18) @ X19))
% 0.66/0.84          | ~ (v1_relat_1 @ X19))),
% 0.66/0.84      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.66/0.84  thf(t43_funct_1, axiom,
% 0.66/0.84    (![A:$i,B:$i]:
% 0.66/0.84     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.66/0.84       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.66/0.84  thf('11', plain,
% 0.66/0.84      (![X22 : $i, X23 : $i]:
% 0.66/0.84         ((k5_relat_1 @ (k6_relat_1 @ X23) @ (k6_relat_1 @ X22))
% 0.66/0.84           = (k6_relat_1 @ (k3_xboole_0 @ X22 @ X23)))),
% 0.66/0.84      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.66/0.84  thf('12', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.66/0.84            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.66/0.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['10', '11'])).
% 0.66/0.84  thf('13', plain, (![X20 : $i]: (v1_relat_1 @ (k6_relat_1 @ X20))),
% 0.66/0.84      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.66/0.84  thf('14', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.66/0.84           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.66/0.84      inference('demod', [status(thm)], ['12', '13'])).
% 0.66/0.84  thf('15', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.66/0.84           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['9', '14'])).
% 0.66/0.84  thf('16', plain, (![X16 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 0.66/0.84      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.66/0.84  thf('17', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.66/0.84           = (k3_xboole_0 @ X0 @ X1))),
% 0.66/0.84      inference('sup+', [status(thm)], ['15', '16'])).
% 0.66/0.84  thf('18', plain, (![X20 : $i]: (v1_relat_1 @ (k6_relat_1 @ X20))),
% 0.66/0.84      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.66/0.84  thf('19', plain, (![X20 : $i]: (v1_relat_1 @ (k6_relat_1 @ X20))),
% 0.66/0.84      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.66/0.84  thf('20', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k3_xboole_0 @ X0 @ X1) = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.66/0.84      inference('demod', [status(thm)], ['8', '17', '18', '19'])).
% 0.66/0.84  thf('21', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         (((k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))
% 0.66/0.84            = (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0))
% 0.66/0.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X2))
% 0.66/0.84          | ~ (v1_relat_1 @ X1))),
% 0.66/0.84      inference('sup+', [status(thm)], ['1', '20'])).
% 0.66/0.84  thf('22', plain, (![X20 : $i]: (v1_relat_1 @ (k6_relat_1 @ X20))),
% 0.66/0.84      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.66/0.84  thf('23', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         (((k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))
% 0.66/0.84            = (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0))
% 0.66/0.84          | ~ (v1_relat_1 @ X1))),
% 0.66/0.84      inference('demod', [status(thm)], ['21', '22'])).
% 0.66/0.84  thf('24', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         (((k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2))
% 0.66/0.84            = (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2))
% 0.66/0.84          | ~ (v1_relat_1 @ X1)
% 0.66/0.84          | ~ (v1_relat_1 @ X1))),
% 0.66/0.84      inference('sup+', [status(thm)], ['0', '23'])).
% 0.66/0.84  thf('25', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         (~ (v1_relat_1 @ X1)
% 0.66/0.84          | ((k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2))
% 0.66/0.84              = (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)))),
% 0.66/0.84      inference('simplify', [status(thm)], ['24'])).
% 0.66/0.84  thf(t139_funct_1, conjecture,
% 0.66/0.84    (![A:$i,B:$i,C:$i]:
% 0.66/0.84     ( ( v1_relat_1 @ C ) =>
% 0.66/0.84       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.66/0.84         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.66/0.84  thf(zf_stmt_0, negated_conjecture,
% 0.66/0.84    (~( ![A:$i,B:$i,C:$i]:
% 0.66/0.84        ( ( v1_relat_1 @ C ) =>
% 0.66/0.84          ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.66/0.84            ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )),
% 0.66/0.84    inference('cnf.neg', [status(esa)], [t139_funct_1])).
% 0.66/0.84  thf('26', plain,
% 0.66/0.84      (((k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B)
% 0.66/0.84         != (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_C @ sk_B)))),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('27', plain,
% 0.66/0.84      ((((k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B)
% 0.66/0.84          != (k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B))
% 0.66/0.84        | ~ (v1_relat_1 @ sk_C))),
% 0.66/0.84      inference('sup-', [status(thm)], ['25', '26'])).
% 0.66/0.84  thf('28', plain, ((v1_relat_1 @ sk_C)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('29', plain,
% 0.66/0.84      (((k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B)
% 0.66/0.84         != (k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B))),
% 0.66/0.84      inference('demod', [status(thm)], ['27', '28'])).
% 0.66/0.84  thf('30', plain, ($false), inference('simplify', [status(thm)], ['29'])).
% 0.66/0.84  
% 0.66/0.84  % SZS output end Refutation
% 0.66/0.84  
% 0.66/0.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
