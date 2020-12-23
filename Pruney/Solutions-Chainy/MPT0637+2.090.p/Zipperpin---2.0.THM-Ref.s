%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GDEkzySvKZ

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:09 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   55 (  71 expanded)
%              Number of leaves         :   22 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :  366 ( 525 expanded)
%              Number of equality atoms :   32 (  38 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k8_relat_1 @ X13 @ X12 )
        = ( k5_relat_1 @ X12 @ ( k6_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t43_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_funct_1])).

thf('1',plain,(
    ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
     != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc24_relat_1,axiom,(
    ! [A: $i] :
      ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('4',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X23: $i] :
      ( v4_relat_1 @ ( k6_relat_1 @ X23 ) @ X23 ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X16
        = ( k7_relat_1 @ X16 @ X17 ) )
      | ~ ( v4_relat_1 @ X16 @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k6_relat_1 @ X0 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k6_relat_1 @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('10',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) @ X11 )
        = ( k7_relat_1 @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k8_relat_1 @ X13 @ X12 )
        = ( k5_relat_1 @ X12 @ ( k6_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('15',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k7_relat_1 @ X21 @ X20 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X20 ) @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('18',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['13','19','20'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('23',plain,(
    ! [X19: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('24',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ( ( k8_relat_1 @ X15 @ X14 )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','28'])).

thf('30',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','29'])).

thf('31',plain,(
    $false ),
    inference(simplify,[status(thm)],['30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GDEkzySvKZ
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:25:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 32 iterations in 0.020s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.49  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.22/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.49  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.49  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(t123_relat_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( v1_relat_1 @ B ) =>
% 0.22/0.49       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      (![X12 : $i, X13 : $i]:
% 0.22/0.49         (((k8_relat_1 @ X13 @ X12) = (k5_relat_1 @ X12 @ (k6_relat_1 @ X13)))
% 0.22/0.49          | ~ (v1_relat_1 @ X12))),
% 0.22/0.49      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.22/0.49  thf(t43_funct_1, conjecture,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.22/0.49       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i,B:$i]:
% 0.22/0.49        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.22/0.49          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.22/0.49         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      ((((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.22/0.49          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 0.22/0.49        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.49  thf(fc24_relat_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.22/0.49       ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.22/0.49       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.22/0.49  thf('3', plain, (![X22 : $i]: (v1_relat_1 @ (k6_relat_1 @ X22))),
% 0.22/0.49      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.22/0.49         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.49      inference('demod', [status(thm)], ['2', '3'])).
% 0.22/0.49  thf('5', plain, (![X23 : $i]: (v4_relat_1 @ (k6_relat_1 @ X23) @ X23)),
% 0.22/0.49      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.22/0.49  thf(t209_relat_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.22/0.49       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      (![X16 : $i, X17 : $i]:
% 0.22/0.49         (((X16) = (k7_relat_1 @ X16 @ X17))
% 0.22/0.49          | ~ (v4_relat_1 @ X16 @ X17)
% 0.22/0.49          | ~ (v1_relat_1 @ X16))),
% 0.22/0.49      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.22/0.49          | ((k6_relat_1 @ X0) = (k7_relat_1 @ (k6_relat_1 @ X0) @ X0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.49  thf('8', plain, (![X22 : $i]: (v1_relat_1 @ (k6_relat_1 @ X22))),
% 0.22/0.49      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      (![X0 : $i]: ((k6_relat_1 @ X0) = (k7_relat_1 @ (k6_relat_1 @ X0) @ X0))),
% 0.22/0.49      inference('demod', [status(thm)], ['7', '8'])).
% 0.22/0.49  thf(t100_relat_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( v1_relat_1 @ C ) =>
% 0.22/0.49       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.22/0.49         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.49         (((k7_relat_1 @ (k7_relat_1 @ X9 @ X10) @ X11)
% 0.22/0.49            = (k7_relat_1 @ X9 @ (k3_xboole_0 @ X10 @ X11)))
% 0.22/0.49          | ~ (v1_relat_1 @ X9))),
% 0.22/0.49      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.22/0.49            = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))
% 0.22/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.22/0.49      inference('sup+', [status(thm)], ['9', '10'])).
% 0.22/0.49  thf('12', plain, (![X22 : $i]: (v1_relat_1 @ (k6_relat_1 @ X22))),
% 0.22/0.49      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.22/0.49           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.22/0.49      inference('demod', [status(thm)], ['11', '12'])).
% 0.22/0.49  thf('14', plain,
% 0.22/0.49      (![X12 : $i, X13 : $i]:
% 0.22/0.49         (((k8_relat_1 @ X13 @ X12) = (k5_relat_1 @ X12 @ (k6_relat_1 @ X13)))
% 0.22/0.49          | ~ (v1_relat_1 @ X12))),
% 0.22/0.49      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.22/0.49  thf(t94_relat_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( v1_relat_1 @ B ) =>
% 0.22/0.49       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      (![X20 : $i, X21 : $i]:
% 0.22/0.49         (((k7_relat_1 @ X21 @ X20) = (k5_relat_1 @ (k6_relat_1 @ X20) @ X21))
% 0.22/0.49          | ~ (v1_relat_1 @ X21))),
% 0.22/0.49      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.22/0.49            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.22/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.22/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.22/0.49      inference('sup+', [status(thm)], ['14', '15'])).
% 0.22/0.49  thf('17', plain, (![X22 : $i]: (v1_relat_1 @ (k6_relat_1 @ X22))),
% 0.22/0.49      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.22/0.49  thf('18', plain, (![X22 : $i]: (v1_relat_1 @ (k6_relat_1 @ X22))),
% 0.22/0.49      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.22/0.49           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.22/0.49      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.22/0.49           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.22/0.49      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.22/0.49  thf('21', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.22/0.49           = (k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))))),
% 0.22/0.49      inference('demod', [status(thm)], ['13', '19', '20'])).
% 0.22/0.49  thf(t17_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.22/0.49  thf('22', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.22/0.49      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.22/0.49  thf(t71_relat_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.22/0.49       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.22/0.49  thf('23', plain, (![X19 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X19)) = (X19))),
% 0.22/0.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.49  thf(t125_relat_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( v1_relat_1 @ B ) =>
% 0.22/0.49       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.22/0.49         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.22/0.49  thf('24', plain,
% 0.22/0.49      (![X14 : $i, X15 : $i]:
% 0.22/0.49         (~ (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 0.22/0.49          | ((k8_relat_1 @ X15 @ X14) = (X14))
% 0.22/0.49          | ~ (v1_relat_1 @ X14))),
% 0.22/0.49      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.22/0.49  thf('25', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (r1_tarski @ X0 @ X1)
% 0.22/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.22/0.49          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.49  thf('26', plain, (![X22 : $i]: (v1_relat_1 @ (k6_relat_1 @ X22))),
% 0.22/0.49      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.22/0.49  thf('27', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (r1_tarski @ X0 @ X1)
% 0.22/0.49          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 0.22/0.49      inference('demod', [status(thm)], ['25', '26'])).
% 0.22/0.49  thf('28', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 0.22/0.49           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['22', '27'])).
% 0.22/0.49  thf('29', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.22/0.49           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.22/0.49      inference('sup+', [status(thm)], ['21', '28'])).
% 0.22/0.49  thf('30', plain,
% 0.22/0.49      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.22/0.49         != (k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B)))),
% 0.22/0.49      inference('demod', [status(thm)], ['4', '29'])).
% 0.22/0.49  thf('31', plain, ($false), inference('simplify', [status(thm)], ['30'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
