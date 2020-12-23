%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fOodG0bwJ6

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:31 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   50 (  56 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :  291 ( 336 expanded)
%              Number of equality atoms :   25 (  30 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X22: $i] :
      ( ( ( k3_relat_1 @ X22 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X22 ) @ ( k2_relat_1 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('1',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t9_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X19 @ X20 )
      | ( r1_tarski @ ( k2_xboole_0 @ X19 @ X21 ) @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t9_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','7'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('9',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X27 ) @ X28 )
      | ( ( k8_relat_1 @ X28 @ X27 )
        = X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ ( k3_relat_1 @ X0 ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ ( k3_relat_1 @ X0 ) @ X0 )
        = X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X22: $i] :
      ( ( ( k3_relat_1 @ X22 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X22 ) @ ( k2_relat_1 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('15',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X31 ) @ X32 )
      | ( ( k7_relat_1 @ X31 @ X32 )
        = X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k3_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ X0 @ ( k3_relat_1 @ X0 ) )
        = X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t18_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_wellord1 @ B @ A )
        = ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ) )).

thf('18',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k2_wellord1 @ X34 @ X33 )
        = ( k8_relat_1 @ X33 @ ( k7_relat_1 @ X34 @ X33 ) ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t18_wellord1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
        = ( k8_relat_1 @ ( k3_relat_1 @ X0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
        = ( k8_relat_1 @ ( k3_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t30_wellord1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k2_wellord1 @ A @ ( k3_relat_1 @ A ) )
        = A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( k2_wellord1 @ A @ ( k3_relat_1 @ A ) )
          = A ) ) ),
    inference('cnf.neg',[status(esa)],[t30_wellord1])).

thf('21',plain,(
    ( k2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( k8_relat_1 @ ( k3_relat_1 @ sk_A ) @ sk_A )
     != sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ( k8_relat_1 @ ( k3_relat_1 @ sk_A ) @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    $false ),
    inference(simplify,[status(thm)],['27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fOodG0bwJ6
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:10:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.45/0.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.69  % Solved by: fo/fo7.sh
% 0.45/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.69  % done 665 iterations in 0.233s
% 0.45/0.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.69  % SZS output start Refutation
% 0.45/0.69  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.45/0.69  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.69  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.69  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.45/0.69  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.45/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.69  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.45/0.69  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.69  thf(d6_relat_1, axiom,
% 0.45/0.69    (![A:$i]:
% 0.45/0.69     ( ( v1_relat_1 @ A ) =>
% 0.45/0.69       ( ( k3_relat_1 @ A ) =
% 0.45/0.69         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.45/0.69  thf('0', plain,
% 0.45/0.69      (![X22 : $i]:
% 0.45/0.69         (((k3_relat_1 @ X22)
% 0.45/0.69            = (k2_xboole_0 @ (k1_relat_1 @ X22) @ (k2_relat_1 @ X22)))
% 0.45/0.69          | ~ (v1_relat_1 @ X22))),
% 0.45/0.69      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.45/0.69  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.45/0.69  thf('1', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.45/0.69      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.69  thf(t9_xboole_1, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i]:
% 0.45/0.69     ( ( r1_tarski @ A @ B ) =>
% 0.45/0.69       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.45/0.69  thf('2', plain,
% 0.45/0.69      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.45/0.69         (~ (r1_tarski @ X19 @ X20)
% 0.45/0.69          | (r1_tarski @ (k2_xboole_0 @ X19 @ X21) @ (k2_xboole_0 @ X20 @ X21)))),
% 0.45/0.69      inference('cnf', [status(esa)], [t9_xboole_1])).
% 0.45/0.69  thf('3', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         (r1_tarski @ (k2_xboole_0 @ k1_xboole_0 @ X1) @ 
% 0.45/0.69          (k2_xboole_0 @ X0 @ X1))),
% 0.45/0.69      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.69  thf('4', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.45/0.69      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.69  thf(t12_xboole_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.45/0.69  thf('5', plain,
% 0.45/0.69      (![X6 : $i, X7 : $i]:
% 0.45/0.69         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.45/0.69      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.45/0.69  thf('6', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.45/0.69      inference('sup-', [status(thm)], ['4', '5'])).
% 0.45/0.69  thf('7', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ X1))),
% 0.45/0.69      inference('demod', [status(thm)], ['3', '6'])).
% 0.45/0.69  thf('8', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((r1_tarski @ (k2_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 0.45/0.69          | ~ (v1_relat_1 @ X0))),
% 0.45/0.69      inference('sup+', [status(thm)], ['0', '7'])).
% 0.45/0.69  thf(t125_relat_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( v1_relat_1 @ B ) =>
% 0.45/0.69       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.45/0.69         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.45/0.69  thf('9', plain,
% 0.45/0.69      (![X27 : $i, X28 : $i]:
% 0.45/0.69         (~ (r1_tarski @ (k2_relat_1 @ X27) @ X28)
% 0.45/0.69          | ((k8_relat_1 @ X28 @ X27) = (X27))
% 0.45/0.69          | ~ (v1_relat_1 @ X27))),
% 0.45/0.69      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.45/0.69  thf('10', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (~ (v1_relat_1 @ X0)
% 0.45/0.69          | ~ (v1_relat_1 @ X0)
% 0.45/0.69          | ((k8_relat_1 @ (k3_relat_1 @ X0) @ X0) = (X0)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['8', '9'])).
% 0.45/0.69  thf('11', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (((k8_relat_1 @ (k3_relat_1 @ X0) @ X0) = (X0)) | ~ (v1_relat_1 @ X0))),
% 0.45/0.69      inference('simplify', [status(thm)], ['10'])).
% 0.45/0.69  thf('12', plain,
% 0.45/0.69      (![X22 : $i]:
% 0.45/0.69         (((k3_relat_1 @ X22)
% 0.45/0.69            = (k2_xboole_0 @ (k1_relat_1 @ X22) @ (k2_relat_1 @ X22)))
% 0.45/0.69          | ~ (v1_relat_1 @ X22))),
% 0.45/0.69      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.45/0.69  thf(t7_xboole_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.45/0.69  thf('13', plain,
% 0.45/0.69      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 0.45/0.69      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.45/0.69  thf('14', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 0.45/0.69          | ~ (v1_relat_1 @ X0))),
% 0.45/0.69      inference('sup+', [status(thm)], ['12', '13'])).
% 0.45/0.69  thf(t97_relat_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( v1_relat_1 @ B ) =>
% 0.45/0.69       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.45/0.69         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.45/0.69  thf('15', plain,
% 0.45/0.69      (![X31 : $i, X32 : $i]:
% 0.45/0.69         (~ (r1_tarski @ (k1_relat_1 @ X31) @ X32)
% 0.45/0.69          | ((k7_relat_1 @ X31 @ X32) = (X31))
% 0.45/0.69          | ~ (v1_relat_1 @ X31))),
% 0.45/0.69      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.45/0.69  thf('16', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (~ (v1_relat_1 @ X0)
% 0.45/0.69          | ~ (v1_relat_1 @ X0)
% 0.45/0.69          | ((k7_relat_1 @ X0 @ (k3_relat_1 @ X0)) = (X0)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['14', '15'])).
% 0.45/0.69  thf('17', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (((k7_relat_1 @ X0 @ (k3_relat_1 @ X0)) = (X0)) | ~ (v1_relat_1 @ X0))),
% 0.45/0.69      inference('simplify', [status(thm)], ['16'])).
% 0.45/0.69  thf(t18_wellord1, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( v1_relat_1 @ B ) =>
% 0.45/0.69       ( ( k2_wellord1 @ B @ A ) = ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ))).
% 0.45/0.69  thf('18', plain,
% 0.45/0.69      (![X33 : $i, X34 : $i]:
% 0.45/0.69         (((k2_wellord1 @ X34 @ X33)
% 0.45/0.69            = (k8_relat_1 @ X33 @ (k7_relat_1 @ X34 @ X33)))
% 0.45/0.69          | ~ (v1_relat_1 @ X34))),
% 0.45/0.69      inference('cnf', [status(esa)], [t18_wellord1])).
% 0.45/0.69  thf('19', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (((k2_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.45/0.69            = (k8_relat_1 @ (k3_relat_1 @ X0) @ X0))
% 0.45/0.69          | ~ (v1_relat_1 @ X0)
% 0.45/0.69          | ~ (v1_relat_1 @ X0))),
% 0.45/0.69      inference('sup+', [status(thm)], ['17', '18'])).
% 0.45/0.69  thf('20', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (~ (v1_relat_1 @ X0)
% 0.45/0.69          | ((k2_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.45/0.69              = (k8_relat_1 @ (k3_relat_1 @ X0) @ X0)))),
% 0.45/0.69      inference('simplify', [status(thm)], ['19'])).
% 0.45/0.69  thf(t30_wellord1, conjecture,
% 0.45/0.69    (![A:$i]:
% 0.45/0.69     ( ( v1_relat_1 @ A ) =>
% 0.45/0.69       ( ( k2_wellord1 @ A @ ( k3_relat_1 @ A ) ) = ( A ) ) ))).
% 0.45/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.69    (~( ![A:$i]:
% 0.45/0.69        ( ( v1_relat_1 @ A ) =>
% 0.45/0.69          ( ( k2_wellord1 @ A @ ( k3_relat_1 @ A ) ) = ( A ) ) ) )),
% 0.45/0.69    inference('cnf.neg', [status(esa)], [t30_wellord1])).
% 0.45/0.69  thf('21', plain, (((k2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A)) != (sk_A))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('22', plain,
% 0.45/0.69      ((((k8_relat_1 @ (k3_relat_1 @ sk_A) @ sk_A) != (sk_A))
% 0.45/0.69        | ~ (v1_relat_1 @ sk_A))),
% 0.45/0.69      inference('sup-', [status(thm)], ['20', '21'])).
% 0.45/0.69  thf('23', plain, ((v1_relat_1 @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('24', plain, (((k8_relat_1 @ (k3_relat_1 @ sk_A) @ sk_A) != (sk_A))),
% 0.45/0.69      inference('demod', [status(thm)], ['22', '23'])).
% 0.45/0.69  thf('25', plain, ((((sk_A) != (sk_A)) | ~ (v1_relat_1 @ sk_A))),
% 0.45/0.69      inference('sup-', [status(thm)], ['11', '24'])).
% 0.45/0.69  thf('26', plain, ((v1_relat_1 @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('27', plain, (((sk_A) != (sk_A))),
% 0.45/0.69      inference('demod', [status(thm)], ['25', '26'])).
% 0.45/0.69  thf('28', plain, ($false), inference('simplify', [status(thm)], ['27'])).
% 0.45/0.69  
% 0.45/0.69  % SZS output end Refutation
% 0.45/0.69  
% 0.45/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
