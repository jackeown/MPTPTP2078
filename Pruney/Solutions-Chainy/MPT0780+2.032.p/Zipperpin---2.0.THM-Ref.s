%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.N4yh8oPoz4

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:29 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   52 (  60 expanded)
%              Number of leaves         :   23 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :  323 ( 413 expanded)
%              Number of equality atoms :   32 (  41 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t26_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
        = ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X21 @ X22 ) @ X23 )
        = ( k2_wellord1 @ X21 @ ( k3_xboole_0 @ X22 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t26_wellord1])).

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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X21 @ X22 ) @ X23 )
        = ( k2_wellord1 @ X21 @ ( k1_setfam_1 @ ( k2_tarski @ X22 @ X23 ) ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

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

thf('3',plain,(
    ( k2_wellord1 @ ( k2_wellord1 @ sk_C @ sk_B ) @ sk_A )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( ( k2_wellord1 @ sk_C @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ sk_A ) ) )
     != ( k2_wellord1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ( k2_wellord1 @ sk_C @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ sk_A ) ) )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('8',plain,(
    ! [X16: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('9',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ( ( k8_relat_1 @ X14 @ X13 )
        = X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k8_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X20 ) @ ( k6_relat_1 @ X19 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('15',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('16',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X20 ) @ ( k6_relat_1 @ X19 ) )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k8_relat_1 @ X12 @ X11 )
        = ( k5_relat_1 @ X11 @ ( k6_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X15: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['13','22'])).

thf('24',plain,(
    ! [X15: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('25',plain,
    ( sk_A
    = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ( k2_wellord1 @ sk_C @ sk_A )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['6','25'])).

thf('27',plain,(
    $false ),
    inference(simplify,[status(thm)],['26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.N4yh8oPoz4
% 0.14/0.36  % Computer   : n009.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 12:10:41 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.23/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.50  % Solved by: fo/fo7.sh
% 0.23/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.50  % done 39 iterations in 0.023s
% 0.23/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.50  % SZS output start Refutation
% 0.23/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.23/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.50  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.23/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.50  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.23/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.23/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.23/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.23/0.50  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.23/0.50  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.23/0.50  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.23/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.50  thf(t26_wellord1, axiom,
% 0.23/0.50    (![A:$i,B:$i,C:$i]:
% 0.23/0.50     ( ( v1_relat_1 @ C ) =>
% 0.23/0.50       ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 0.23/0.50         ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.23/0.50  thf('0', plain,
% 0.23/0.50      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.23/0.50         (((k2_wellord1 @ (k2_wellord1 @ X21 @ X22) @ X23)
% 0.23/0.50            = (k2_wellord1 @ X21 @ (k3_xboole_0 @ X22 @ X23)))
% 0.23/0.50          | ~ (v1_relat_1 @ X21))),
% 0.23/0.50      inference('cnf', [status(esa)], [t26_wellord1])).
% 0.23/0.50  thf(t12_setfam_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.23/0.50  thf('1', plain,
% 0.23/0.50      (![X9 : $i, X10 : $i]:
% 0.23/0.50         ((k1_setfam_1 @ (k2_tarski @ X9 @ X10)) = (k3_xboole_0 @ X9 @ X10))),
% 0.23/0.50      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.23/0.50  thf('2', plain,
% 0.23/0.50      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.23/0.50         (((k2_wellord1 @ (k2_wellord1 @ X21 @ X22) @ X23)
% 0.23/0.50            = (k2_wellord1 @ X21 @ (k1_setfam_1 @ (k2_tarski @ X22 @ X23))))
% 0.23/0.50          | ~ (v1_relat_1 @ X21))),
% 0.23/0.50      inference('demod', [status(thm)], ['0', '1'])).
% 0.23/0.50  thf(t29_wellord1, conjecture,
% 0.23/0.50    (![A:$i,B:$i,C:$i]:
% 0.23/0.50     ( ( v1_relat_1 @ C ) =>
% 0.23/0.50       ( ( r1_tarski @ A @ B ) =>
% 0.23/0.50         ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 0.23/0.50           ( k2_wellord1 @ C @ A ) ) ) ))).
% 0.23/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.23/0.50        ( ( v1_relat_1 @ C ) =>
% 0.23/0.50          ( ( r1_tarski @ A @ B ) =>
% 0.23/0.50            ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 0.23/0.50              ( k2_wellord1 @ C @ A ) ) ) ) )),
% 0.23/0.50    inference('cnf.neg', [status(esa)], [t29_wellord1])).
% 0.23/0.50  thf('3', plain,
% 0.23/0.50      (((k2_wellord1 @ (k2_wellord1 @ sk_C @ sk_B) @ sk_A)
% 0.23/0.50         != (k2_wellord1 @ sk_C @ sk_A))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('4', plain,
% 0.23/0.50      ((((k2_wellord1 @ sk_C @ (k1_setfam_1 @ (k2_tarski @ sk_B @ sk_A)))
% 0.23/0.50          != (k2_wellord1 @ sk_C @ sk_A))
% 0.23/0.50        | ~ (v1_relat_1 @ sk_C))),
% 0.23/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.23/0.50  thf('5', plain, ((v1_relat_1 @ sk_C)),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('6', plain,
% 0.23/0.50      (((k2_wellord1 @ sk_C @ (k1_setfam_1 @ (k2_tarski @ sk_B @ sk_A)))
% 0.23/0.50         != (k2_wellord1 @ sk_C @ sk_A))),
% 0.23/0.50      inference('demod', [status(thm)], ['4', '5'])).
% 0.23/0.50  thf('7', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf(t71_relat_1, axiom,
% 0.23/0.50    (![A:$i]:
% 0.23/0.50     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.23/0.50       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.23/0.50  thf('8', plain, (![X16 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 0.23/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.23/0.50  thf(t125_relat_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( v1_relat_1 @ B ) =>
% 0.23/0.50       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.23/0.50         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.23/0.50  thf('9', plain,
% 0.23/0.50      (![X13 : $i, X14 : $i]:
% 0.23/0.50         (~ (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 0.23/0.50          | ((k8_relat_1 @ X14 @ X13) = (X13))
% 0.23/0.50          | ~ (v1_relat_1 @ X13))),
% 0.23/0.50      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.23/0.50  thf('10', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]:
% 0.23/0.50         (~ (r1_tarski @ X0 @ X1)
% 0.23/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.23/0.50          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 0.23/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.23/0.50  thf(fc3_funct_1, axiom,
% 0.23/0.50    (![A:$i]:
% 0.23/0.50     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.23/0.50       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.23/0.50  thf('11', plain, (![X17 : $i]: (v1_relat_1 @ (k6_relat_1 @ X17))),
% 0.23/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.23/0.50  thf('12', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]:
% 0.23/0.50         (~ (r1_tarski @ X0 @ X1)
% 0.23/0.50          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 0.23/0.50      inference('demod', [status(thm)], ['10', '11'])).
% 0.23/0.50  thf('13', plain,
% 0.23/0.50      (((k8_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)) = (k6_relat_1 @ sk_A))),
% 0.23/0.50      inference('sup-', [status(thm)], ['7', '12'])).
% 0.23/0.50  thf(t43_funct_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.23/0.50       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.23/0.50  thf('14', plain,
% 0.23/0.50      (![X19 : $i, X20 : $i]:
% 0.23/0.50         ((k5_relat_1 @ (k6_relat_1 @ X20) @ (k6_relat_1 @ X19))
% 0.23/0.50           = (k6_relat_1 @ (k3_xboole_0 @ X19 @ X20)))),
% 0.23/0.50      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.23/0.50  thf('15', plain,
% 0.23/0.50      (![X9 : $i, X10 : $i]:
% 0.23/0.50         ((k1_setfam_1 @ (k2_tarski @ X9 @ X10)) = (k3_xboole_0 @ X9 @ X10))),
% 0.23/0.50      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.23/0.50  thf('16', plain,
% 0.23/0.50      (![X19 : $i, X20 : $i]:
% 0.23/0.50         ((k5_relat_1 @ (k6_relat_1 @ X20) @ (k6_relat_1 @ X19))
% 0.23/0.50           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X19 @ X20))))),
% 0.23/0.50      inference('demod', [status(thm)], ['14', '15'])).
% 0.23/0.50  thf(t123_relat_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( v1_relat_1 @ B ) =>
% 0.23/0.50       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.23/0.50  thf('17', plain,
% 0.23/0.50      (![X11 : $i, X12 : $i]:
% 0.23/0.50         (((k8_relat_1 @ X12 @ X11) = (k5_relat_1 @ X11 @ (k6_relat_1 @ X12)))
% 0.23/0.50          | ~ (v1_relat_1 @ X11))),
% 0.23/0.50      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.23/0.50  thf('18', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]:
% 0.23/0.50         (((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.23/0.50            = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))
% 0.23/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.23/0.50      inference('sup+', [status(thm)], ['16', '17'])).
% 0.23/0.50  thf('19', plain, (![X17 : $i]: (v1_relat_1 @ (k6_relat_1 @ X17))),
% 0.23/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.23/0.50  thf('20', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]:
% 0.23/0.50         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.23/0.50           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.23/0.50      inference('demod', [status(thm)], ['18', '19'])).
% 0.23/0.50  thf('21', plain, (![X15 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X15)) = (X15))),
% 0.23/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.23/0.50  thf('22', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]:
% 0.23/0.50         ((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.23/0.50           = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 0.23/0.50      inference('sup+', [status(thm)], ['20', '21'])).
% 0.23/0.50  thf('23', plain,
% 0.23/0.50      (((k1_relat_1 @ (k6_relat_1 @ sk_A))
% 0.23/0.50         = (k1_setfam_1 @ (k2_tarski @ sk_B @ sk_A)))),
% 0.23/0.50      inference('sup+', [status(thm)], ['13', '22'])).
% 0.23/0.50  thf('24', plain, (![X15 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X15)) = (X15))),
% 0.23/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.23/0.50  thf('25', plain, (((sk_A) = (k1_setfam_1 @ (k2_tarski @ sk_B @ sk_A)))),
% 0.23/0.50      inference('demod', [status(thm)], ['23', '24'])).
% 0.23/0.50  thf('26', plain,
% 0.23/0.50      (((k2_wellord1 @ sk_C @ sk_A) != (k2_wellord1 @ sk_C @ sk_A))),
% 0.23/0.50      inference('demod', [status(thm)], ['6', '25'])).
% 0.23/0.50  thf('27', plain, ($false), inference('simplify', [status(thm)], ['26'])).
% 0.23/0.50  
% 0.23/0.50  % SZS output end Refutation
% 0.23/0.50  
% 0.23/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
