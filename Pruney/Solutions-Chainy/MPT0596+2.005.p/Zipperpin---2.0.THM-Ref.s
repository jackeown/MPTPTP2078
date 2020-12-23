%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.q448UeBDWg

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:38 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   53 (  65 expanded)
%              Number of leaves         :   20 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :  407 ( 620 expanded)
%              Number of equality atoms :   24 (  35 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k7_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X15 ) @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k8_relat_1 @ X5 @ X4 )
        = ( k5_relat_1 @ X4 @ ( k6_relat_1 @ X5 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) @ X12 )
        = ( k5_relat_1 @ X11 @ ( k5_relat_1 @ X10 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('4',plain,(
    ! [X3: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k8_relat_1 @ X0 @ X2 ) @ X1 )
        = ( k5_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k8_relat_1 @ X0 @ X2 ) @ X1 )
        = ( k5_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t200_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ C @ A ) ) )
           => ( ( k5_relat_1 @ B @ ( k7_relat_1 @ C @ A ) )
              = ( k5_relat_1 @ B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ! [C: $i] :
            ( ( v1_relat_1 @ C )
           => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ C @ A ) ) )
             => ( ( k5_relat_1 @ B @ ( k7_relat_1 @ C @ A ) )
                = ( k5_relat_1 @ B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t200_relat_1])).

thf('9',plain,(
    ( k5_relat_1 @ sk_B @ ( k7_relat_1 @ sk_C @ sk_A ) )
 != ( k5_relat_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k5_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) @ sk_C )
     != ( k5_relat_1 @ sk_B @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k7_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X15 ) @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) ) @ ( k1_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('14',plain,(
    ! [X13: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('15',plain,(
    ! [X3: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['21','22'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('24',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X6 ) @ X7 )
      | ( ( k8_relat_1 @ X7 @ X6 )
        = X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k8_relat_1 @ sk_A @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k8_relat_1 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ( k5_relat_1 @ sk_B @ sk_C )
 != ( k5_relat_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['10','27','28','29'])).

thf('31',plain,(
    $false ),
    inference(simplify,[status(thm)],['30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.q448UeBDWg
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:35:39 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.54/0.75  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.54/0.75  % Solved by: fo/fo7.sh
% 0.54/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.75  % done 417 iterations in 0.291s
% 0.54/0.75  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.54/0.75  % SZS output start Refutation
% 0.54/0.75  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.54/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.75  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.54/0.75  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.54/0.75  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.54/0.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.75  thf(sk_C_type, type, sk_C: $i).
% 0.54/0.75  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.54/0.75  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.75  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.54/0.75  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.54/0.75  thf(t94_relat_1, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( v1_relat_1 @ B ) =>
% 0.54/0.75       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.54/0.75  thf('0', plain,
% 0.54/0.75      (![X15 : $i, X16 : $i]:
% 0.54/0.75         (((k7_relat_1 @ X16 @ X15) = (k5_relat_1 @ (k6_relat_1 @ X15) @ X16))
% 0.54/0.75          | ~ (v1_relat_1 @ X16))),
% 0.54/0.75      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.54/0.75  thf(t123_relat_1, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( v1_relat_1 @ B ) =>
% 0.54/0.75       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.54/0.75  thf('1', plain,
% 0.54/0.75      (![X4 : $i, X5 : $i]:
% 0.54/0.75         (((k8_relat_1 @ X5 @ X4) = (k5_relat_1 @ X4 @ (k6_relat_1 @ X5)))
% 0.54/0.75          | ~ (v1_relat_1 @ X4))),
% 0.54/0.75      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.54/0.75  thf(t55_relat_1, axiom,
% 0.54/0.75    (![A:$i]:
% 0.54/0.75     ( ( v1_relat_1 @ A ) =>
% 0.54/0.75       ( ![B:$i]:
% 0.54/0.75         ( ( v1_relat_1 @ B ) =>
% 0.54/0.75           ( ![C:$i]:
% 0.54/0.75             ( ( v1_relat_1 @ C ) =>
% 0.54/0.75               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.54/0.75                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.54/0.75  thf('2', plain,
% 0.54/0.75      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.54/0.75         (~ (v1_relat_1 @ X10)
% 0.54/0.75          | ((k5_relat_1 @ (k5_relat_1 @ X11 @ X10) @ X12)
% 0.54/0.75              = (k5_relat_1 @ X11 @ (k5_relat_1 @ X10 @ X12)))
% 0.54/0.75          | ~ (v1_relat_1 @ X12)
% 0.54/0.75          | ~ (v1_relat_1 @ X11))),
% 0.54/0.75      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.54/0.75  thf('3', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.75         (((k5_relat_1 @ (k8_relat_1 @ X1 @ X0) @ X2)
% 0.54/0.75            = (k5_relat_1 @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X2)))
% 0.54/0.75          | ~ (v1_relat_1 @ X0)
% 0.54/0.75          | ~ (v1_relat_1 @ X0)
% 0.54/0.75          | ~ (v1_relat_1 @ X2)
% 0.54/0.75          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['1', '2'])).
% 0.54/0.75  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.54/0.75  thf('4', plain, (![X3 : $i]: (v1_relat_1 @ (k6_relat_1 @ X3))),
% 0.54/0.75      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.54/0.75  thf('5', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.75         (((k5_relat_1 @ (k8_relat_1 @ X1 @ X0) @ X2)
% 0.54/0.75            = (k5_relat_1 @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X2)))
% 0.54/0.75          | ~ (v1_relat_1 @ X0)
% 0.54/0.75          | ~ (v1_relat_1 @ X0)
% 0.54/0.75          | ~ (v1_relat_1 @ X2))),
% 0.54/0.75      inference('demod', [status(thm)], ['3', '4'])).
% 0.54/0.75  thf('6', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.75         (~ (v1_relat_1 @ X2)
% 0.54/0.75          | ~ (v1_relat_1 @ X0)
% 0.54/0.75          | ((k5_relat_1 @ (k8_relat_1 @ X1 @ X0) @ X2)
% 0.54/0.75              = (k5_relat_1 @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X2))))),
% 0.54/0.75      inference('simplify', [status(thm)], ['5'])).
% 0.54/0.75  thf('7', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.75         (((k5_relat_1 @ (k8_relat_1 @ X0 @ X2) @ X1)
% 0.54/0.75            = (k5_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0)))
% 0.54/0.75          | ~ (v1_relat_1 @ X1)
% 0.54/0.75          | ~ (v1_relat_1 @ X2)
% 0.54/0.75          | ~ (v1_relat_1 @ X1))),
% 0.54/0.75      inference('sup+', [status(thm)], ['0', '6'])).
% 0.54/0.75  thf('8', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.75         (~ (v1_relat_1 @ X2)
% 0.54/0.75          | ~ (v1_relat_1 @ X1)
% 0.54/0.75          | ((k5_relat_1 @ (k8_relat_1 @ X0 @ X2) @ X1)
% 0.54/0.75              = (k5_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0))))),
% 0.54/0.75      inference('simplify', [status(thm)], ['7'])).
% 0.54/0.75  thf(t200_relat_1, conjecture,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( v1_relat_1 @ B ) =>
% 0.54/0.75       ( ![C:$i]:
% 0.54/0.75         ( ( v1_relat_1 @ C ) =>
% 0.54/0.75           ( ( r1_tarski @
% 0.54/0.75               ( k2_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ C @ A ) ) ) =>
% 0.54/0.75             ( ( k5_relat_1 @ B @ ( k7_relat_1 @ C @ A ) ) =
% 0.54/0.75               ( k5_relat_1 @ B @ C ) ) ) ) ) ))).
% 0.54/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.75    (~( ![A:$i,B:$i]:
% 0.54/0.75        ( ( v1_relat_1 @ B ) =>
% 0.54/0.75          ( ![C:$i]:
% 0.54/0.75            ( ( v1_relat_1 @ C ) =>
% 0.54/0.75              ( ( r1_tarski @
% 0.54/0.75                  ( k2_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ C @ A ) ) ) =>
% 0.54/0.75                ( ( k5_relat_1 @ B @ ( k7_relat_1 @ C @ A ) ) =
% 0.54/0.75                  ( k5_relat_1 @ B @ C ) ) ) ) ) ) )),
% 0.54/0.75    inference('cnf.neg', [status(esa)], [t200_relat_1])).
% 0.54/0.75  thf('9', plain,
% 0.54/0.75      (((k5_relat_1 @ sk_B @ (k7_relat_1 @ sk_C @ sk_A))
% 0.54/0.75         != (k5_relat_1 @ sk_B @ sk_C))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('10', plain,
% 0.54/0.75      ((((k5_relat_1 @ (k8_relat_1 @ sk_A @ sk_B) @ sk_C)
% 0.54/0.75          != (k5_relat_1 @ sk_B @ sk_C))
% 0.54/0.75        | ~ (v1_relat_1 @ sk_C)
% 0.54/0.75        | ~ (v1_relat_1 @ sk_B))),
% 0.54/0.75      inference('sup-', [status(thm)], ['8', '9'])).
% 0.54/0.75  thf('11', plain,
% 0.54/0.75      (![X15 : $i, X16 : $i]:
% 0.54/0.75         (((k7_relat_1 @ X16 @ X15) = (k5_relat_1 @ (k6_relat_1 @ X15) @ X16))
% 0.54/0.75          | ~ (v1_relat_1 @ X16))),
% 0.54/0.75      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.54/0.75  thf(t44_relat_1, axiom,
% 0.54/0.75    (![A:$i]:
% 0.54/0.75     ( ( v1_relat_1 @ A ) =>
% 0.54/0.75       ( ![B:$i]:
% 0.54/0.75         ( ( v1_relat_1 @ B ) =>
% 0.54/0.75           ( r1_tarski @
% 0.54/0.75             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.54/0.75  thf('12', plain,
% 0.54/0.75      (![X8 : $i, X9 : $i]:
% 0.54/0.75         (~ (v1_relat_1 @ X8)
% 0.54/0.75          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X9 @ X8)) @ 
% 0.54/0.75             (k1_relat_1 @ X9))
% 0.54/0.75          | ~ (v1_relat_1 @ X9))),
% 0.54/0.75      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.54/0.75  thf('13', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 0.54/0.75           (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.54/0.75          | ~ (v1_relat_1 @ X1)
% 0.54/0.75          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.54/0.75          | ~ (v1_relat_1 @ X1))),
% 0.54/0.75      inference('sup+', [status(thm)], ['11', '12'])).
% 0.54/0.75  thf(t71_relat_1, axiom,
% 0.54/0.75    (![A:$i]:
% 0.54/0.75     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.54/0.75       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.54/0.75  thf('14', plain, (![X13 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X13)) = (X13))),
% 0.54/0.75      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.54/0.75  thf('15', plain, (![X3 : $i]: (v1_relat_1 @ (k6_relat_1 @ X3))),
% 0.54/0.75      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.54/0.75  thf('16', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0)
% 0.54/0.75          | ~ (v1_relat_1 @ X1)
% 0.54/0.75          | ~ (v1_relat_1 @ X1))),
% 0.54/0.75      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.54/0.75  thf('17', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (~ (v1_relat_1 @ X1)
% 0.54/0.75          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0))),
% 0.54/0.75      inference('simplify', [status(thm)], ['16'])).
% 0.54/0.75  thf('18', plain,
% 0.54/0.75      ((r1_tarski @ (k2_relat_1 @ sk_B) @ 
% 0.54/0.75        (k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf(t1_xboole_1, axiom,
% 0.54/0.75    (![A:$i,B:$i,C:$i]:
% 0.54/0.75     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.54/0.75       ( r1_tarski @ A @ C ) ))).
% 0.54/0.75  thf('19', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.75         (~ (r1_tarski @ X0 @ X1)
% 0.54/0.75          | ~ (r1_tarski @ X1 @ X2)
% 0.54/0.75          | (r1_tarski @ X0 @ X2))),
% 0.54/0.75      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.54/0.75  thf('20', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((r1_tarski @ (k2_relat_1 @ sk_B) @ X0)
% 0.54/0.75          | ~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)) @ X0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['18', '19'])).
% 0.54/0.75  thf('21', plain,
% 0.54/0.75      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_B) @ sk_A))),
% 0.54/0.75      inference('sup-', [status(thm)], ['17', '20'])).
% 0.54/0.75  thf('22', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('23', plain, ((r1_tarski @ (k2_relat_1 @ sk_B) @ sk_A)),
% 0.54/0.75      inference('demod', [status(thm)], ['21', '22'])).
% 0.54/0.75  thf(t125_relat_1, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( v1_relat_1 @ B ) =>
% 0.54/0.75       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.54/0.75         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.54/0.75  thf('24', plain,
% 0.54/0.75      (![X6 : $i, X7 : $i]:
% 0.54/0.75         (~ (r1_tarski @ (k2_relat_1 @ X6) @ X7)
% 0.54/0.75          | ((k8_relat_1 @ X7 @ X6) = (X6))
% 0.54/0.75          | ~ (v1_relat_1 @ X6))),
% 0.54/0.75      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.54/0.75  thf('25', plain,
% 0.54/0.75      ((~ (v1_relat_1 @ sk_B) | ((k8_relat_1 @ sk_A @ sk_B) = (sk_B)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['23', '24'])).
% 0.54/0.75  thf('26', plain, ((v1_relat_1 @ sk_B)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('27', plain, (((k8_relat_1 @ sk_A @ sk_B) = (sk_B))),
% 0.54/0.75      inference('demod', [status(thm)], ['25', '26'])).
% 0.54/0.75  thf('28', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('29', plain, ((v1_relat_1 @ sk_B)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('30', plain,
% 0.54/0.75      (((k5_relat_1 @ sk_B @ sk_C) != (k5_relat_1 @ sk_B @ sk_C))),
% 0.54/0.75      inference('demod', [status(thm)], ['10', '27', '28', '29'])).
% 0.54/0.75  thf('31', plain, ($false), inference('simplify', [status(thm)], ['30'])).
% 0.54/0.75  
% 0.54/0.75  % SZS output end Refutation
% 0.54/0.75  
% 0.63/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
