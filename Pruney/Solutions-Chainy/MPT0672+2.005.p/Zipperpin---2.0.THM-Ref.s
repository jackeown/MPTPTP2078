%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YOQ5GrBz93

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:58 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   53 (  70 expanded)
%              Number of leaves         :   17 (  26 expanded)
%              Depth                    :   12
%              Number of atoms          :  486 ( 848 expanded)
%              Number of equality atoms :   43 (  73 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k8_relat_1 @ X5 @ X4 )
        = ( k5_relat_1 @ X4 @ ( k6_relat_1 @ X5 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k8_relat_1 @ X5 @ X4 )
        = ( k5_relat_1 @ X4 @ ( k6_relat_1 @ X5 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X15 ) @ ( k6_relat_1 @ X14 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k8_relat_1 @ X5 @ X4 )
        = ( k5_relat_1 @ X4 @ ( k6_relat_1 @ X5 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t139_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k8_relat_1 @ A @ ( k5_relat_1 @ B @ C ) )
            = ( k5_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) ) ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k8_relat_1 @ X11 @ ( k5_relat_1 @ X10 @ X9 ) )
        = ( k5_relat_1 @ X10 @ ( k8_relat_1 @ X11 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t139_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ X2 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ X2 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X2 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X2 @ X1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t97_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r1_tarski @ A @ B )
       => ( ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) )
            = ( k8_relat_1 @ A @ C ) )
          & ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) )
            = ( k8_relat_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r1_tarski @ A @ B )
         => ( ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) )
              = ( k8_relat_1 @ A @ C ) )
            & ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) )
              = ( k8_relat_1 @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t97_funct_1])).

thf('15',plain,
    ( ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
    | ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
   <= ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t129_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) )
          = ( k8_relat_1 @ A @ C ) ) ) ) )).

thf('18',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X8 )
      | ( ( k8_relat_1 @ X7 @ ( k8_relat_1 @ X6 @ X8 ) )
        = ( k8_relat_1 @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t129_relat_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ X0 ) )
        = ( k8_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
   <= ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['15'])).

thf('21',plain,
    ( ( ( ( k8_relat_1 @ sk_A @ sk_C )
       != ( k8_relat_1 @ sk_A @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( k8_relat_1 @ sk_A @ sk_C )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
   <= ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
    = ( k8_relat_1 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
    | ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['15'])).

thf('26',plain,(
    ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C ) )
 != ( k8_relat_1 @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['24','25'])).

thf('27',plain,(
    ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C ) )
 != ( k8_relat_1 @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['16','26'])).

thf('28',plain,
    ( ( ( k8_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ sk_C )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','27'])).

thf('29',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('31',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ( k8_relat_1 @ sk_A @ sk_C )
 != ( k8_relat_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['28','31','32'])).

thf('34',plain,(
    $false ),
    inference(simplify,[status(thm)],['33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YOQ5GrBz93
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:34:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 34 iterations in 0.031s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.50  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.50  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.22/0.50  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.22/0.50  thf(t123_relat_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ B ) =>
% 0.22/0.50       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      (![X4 : $i, X5 : $i]:
% 0.22/0.50         (((k8_relat_1 @ X5 @ X4) = (k5_relat_1 @ X4 @ (k6_relat_1 @ X5)))
% 0.22/0.50          | ~ (v1_relat_1 @ X4))),
% 0.22/0.50      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      (![X4 : $i, X5 : $i]:
% 0.22/0.50         (((k8_relat_1 @ X5 @ X4) = (k5_relat_1 @ X4 @ (k6_relat_1 @ X5)))
% 0.22/0.50          | ~ (v1_relat_1 @ X4))),
% 0.22/0.50      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.22/0.50  thf(t43_funct_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.22/0.50       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      (![X14 : $i, X15 : $i]:
% 0.22/0.50         ((k5_relat_1 @ (k6_relat_1 @ X15) @ (k6_relat_1 @ X14))
% 0.22/0.50           = (k6_relat_1 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      (![X4 : $i, X5 : $i]:
% 0.22/0.50         (((k8_relat_1 @ X5 @ X4) = (k5_relat_1 @ X4 @ (k6_relat_1 @ X5)))
% 0.22/0.50          | ~ (v1_relat_1 @ X4))),
% 0.22/0.50      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.22/0.50            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.22/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.22/0.50      inference('sup+', [status(thm)], ['2', '3'])).
% 0.22/0.50  thf(fc3_funct_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.22/0.50       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.22/0.50  thf('5', plain, (![X12 : $i]: (v1_relat_1 @ (k6_relat_1 @ X12))),
% 0.22/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.22/0.50           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.22/0.50      inference('demod', [status(thm)], ['4', '5'])).
% 0.22/0.50  thf(t139_relat_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ B ) =>
% 0.22/0.50       ( ![C:$i]:
% 0.22/0.50         ( ( v1_relat_1 @ C ) =>
% 0.22/0.50           ( ( k8_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) =
% 0.22/0.50             ( k5_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) ) ) ) ))).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ X9)
% 0.22/0.50          | ((k8_relat_1 @ X11 @ (k5_relat_1 @ X10 @ X9))
% 0.22/0.50              = (k5_relat_1 @ X10 @ (k8_relat_1 @ X11 @ X9)))
% 0.22/0.50          | ~ (v1_relat_1 @ X10))),
% 0.22/0.50      inference('cnf', [status(esa)], [t139_relat_1])).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         (((k8_relat_1 @ X1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X0)))
% 0.22/0.50            = (k5_relat_1 @ X2 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))
% 0.22/0.50          | ~ (v1_relat_1 @ X2)
% 0.22/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.22/0.50      inference('sup+', [status(thm)], ['6', '7'])).
% 0.22/0.50  thf('9', plain, (![X12 : $i]: (v1_relat_1 @ (k6_relat_1 @ X12))),
% 0.22/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         (((k8_relat_1 @ X1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X0)))
% 0.22/0.50            = (k5_relat_1 @ X2 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))
% 0.22/0.50          | ~ (v1_relat_1 @ X2))),
% 0.22/0.50      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         (((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0))
% 0.22/0.50            = (k5_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X2 @ X1))))
% 0.22/0.50          | ~ (v1_relat_1 @ X0)
% 0.22/0.50          | ~ (v1_relat_1 @ X0))),
% 0.22/0.50      inference('sup+', [status(thm)], ['1', '10'])).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ X0)
% 0.22/0.50          | ((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0))
% 0.22/0.50              = (k5_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X2 @ X1)))))),
% 0.22/0.50      inference('simplify', [status(thm)], ['11'])).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         (((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0))
% 0.22/0.50            = (k8_relat_1 @ (k3_xboole_0 @ X2 @ X1) @ X0))
% 0.22/0.50          | ~ (v1_relat_1 @ X0)
% 0.22/0.50          | ~ (v1_relat_1 @ X0))),
% 0.22/0.50      inference('sup+', [status(thm)], ['0', '12'])).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ X0)
% 0.22/0.50          | ((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0))
% 0.22/0.50              = (k8_relat_1 @ (k3_xboole_0 @ X2 @ X1) @ X0)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['13'])).
% 0.22/0.50  thf(t97_funct_1, conjecture,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.50       ( ( r1_tarski @ A @ B ) =>
% 0.22/0.50         ( ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) =
% 0.22/0.50             ( k8_relat_1 @ A @ C ) ) & 
% 0.22/0.50           ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) ) =
% 0.22/0.50             ( k8_relat_1 @ A @ C ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.50        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.50          ( ( r1_tarski @ A @ B ) =>
% 0.22/0.50            ( ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) =
% 0.22/0.50                ( k8_relat_1 @ A @ C ) ) & 
% 0.22/0.50              ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) ) =
% 0.22/0.50                ( k8_relat_1 @ A @ C ) ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t97_funct_1])).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      ((((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ sk_C))
% 0.22/0.50          != (k8_relat_1 @ sk_A @ sk_C))
% 0.22/0.50        | ((k8_relat_1 @ sk_A @ (k8_relat_1 @ sk_B @ sk_C))
% 0.22/0.50            != (k8_relat_1 @ sk_A @ sk_C)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      ((((k8_relat_1 @ sk_A @ (k8_relat_1 @ sk_B @ sk_C))
% 0.22/0.50          != (k8_relat_1 @ sk_A @ sk_C)))
% 0.22/0.50         <= (~
% 0.22/0.50             (((k8_relat_1 @ sk_A @ (k8_relat_1 @ sk_B @ sk_C))
% 0.22/0.50                = (k8_relat_1 @ sk_A @ sk_C))))),
% 0.22/0.50      inference('split', [status(esa)], ['15'])).
% 0.22/0.50  thf('17', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t129_relat_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ C ) =>
% 0.22/0.50       ( ( r1_tarski @ A @ B ) =>
% 0.22/0.50         ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) = ( k8_relat_1 @ A @ C ) ) ) ))).
% 0.22/0.50  thf('18', plain,
% 0.22/0.50      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.50         (~ (r1_tarski @ X6 @ X7)
% 0.22/0.50          | ~ (v1_relat_1 @ X8)
% 0.22/0.50          | ((k8_relat_1 @ X7 @ (k8_relat_1 @ X6 @ X8))
% 0.22/0.50              = (k8_relat_1 @ X6 @ X8)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t129_relat_1])).
% 0.22/0.50  thf('19', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ X0))
% 0.22/0.50            = (k8_relat_1 @ sk_A @ X0))
% 0.22/0.50          | ~ (v1_relat_1 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.50  thf('20', plain,
% 0.22/0.50      ((((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ sk_C))
% 0.22/0.50          != (k8_relat_1 @ sk_A @ sk_C)))
% 0.22/0.50         <= (~
% 0.22/0.50             (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ sk_C))
% 0.22/0.50                = (k8_relat_1 @ sk_A @ sk_C))))),
% 0.22/0.50      inference('split', [status(esa)], ['15'])).
% 0.22/0.50  thf('21', plain,
% 0.22/0.50      (((((k8_relat_1 @ sk_A @ sk_C) != (k8_relat_1 @ sk_A @ sk_C))
% 0.22/0.50         | ~ (v1_relat_1 @ sk_C)))
% 0.22/0.50         <= (~
% 0.22/0.50             (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ sk_C))
% 0.22/0.50                = (k8_relat_1 @ sk_A @ sk_C))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.50  thf('22', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('23', plain,
% 0.22/0.50      ((((k8_relat_1 @ sk_A @ sk_C) != (k8_relat_1 @ sk_A @ sk_C)))
% 0.22/0.50         <= (~
% 0.22/0.50             (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ sk_C))
% 0.22/0.50                = (k8_relat_1 @ sk_A @ sk_C))))),
% 0.22/0.50      inference('demod', [status(thm)], ['21', '22'])).
% 0.22/0.50  thf('24', plain,
% 0.22/0.50      ((((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ sk_C))
% 0.22/0.50          = (k8_relat_1 @ sk_A @ sk_C)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['23'])).
% 0.22/0.50  thf('25', plain,
% 0.22/0.50      (~
% 0.22/0.50       (((k8_relat_1 @ sk_A @ (k8_relat_1 @ sk_B @ sk_C))
% 0.22/0.50          = (k8_relat_1 @ sk_A @ sk_C))) | 
% 0.22/0.50       ~
% 0.22/0.50       (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ sk_C))
% 0.22/0.50          = (k8_relat_1 @ sk_A @ sk_C)))),
% 0.22/0.50      inference('split', [status(esa)], ['15'])).
% 0.22/0.50  thf('26', plain,
% 0.22/0.50      (~
% 0.22/0.50       (((k8_relat_1 @ sk_A @ (k8_relat_1 @ sk_B @ sk_C))
% 0.22/0.50          = (k8_relat_1 @ sk_A @ sk_C)))),
% 0.22/0.50      inference('sat_resolution*', [status(thm)], ['24', '25'])).
% 0.22/0.50  thf('27', plain,
% 0.22/0.50      (((k8_relat_1 @ sk_A @ (k8_relat_1 @ sk_B @ sk_C))
% 0.22/0.50         != (k8_relat_1 @ sk_A @ sk_C))),
% 0.22/0.50      inference('simpl_trail', [status(thm)], ['16', '26'])).
% 0.22/0.50  thf('28', plain,
% 0.22/0.50      ((((k8_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B) @ sk_C)
% 0.22/0.50          != (k8_relat_1 @ sk_A @ sk_C))
% 0.22/0.50        | ~ (v1_relat_1 @ sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['14', '27'])).
% 0.22/0.50  thf('29', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t28_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.50  thf('30', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.22/0.50      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.22/0.50  thf('31', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.50  thf('32', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('33', plain,
% 0.22/0.50      (((k8_relat_1 @ sk_A @ sk_C) != (k8_relat_1 @ sk_A @ sk_C))),
% 0.22/0.50      inference('demod', [status(thm)], ['28', '31', '32'])).
% 0.22/0.50  thf('34', plain, ($false), inference('simplify', [status(thm)], ['33'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
