%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rsrpG6mR47

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:40 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   53 (  63 expanded)
%              Number of leaves         :   20 (  28 expanded)
%              Depth                    :   14
%              Number of atoms          :  361 ( 449 expanded)
%              Number of equality atoms :   33 (  40 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k7_relat_1 @ X13 @ X12 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X12 ) @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t162_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
            = ( k9_relat_1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i,C: $i] :
            ( ( r1_tarski @ B @ C )
           => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
              = ( k9_relat_1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t162_relat_1])).

thf('1',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('2',plain,(
    ! [X11: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ( ( k8_relat_1 @ X4 @ X3 )
        = X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k8_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ X1 )
        = ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k7_relat_1 @ X13 @ X12 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X12 ) @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) )
        = ( k9_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k2_relat_1 @ ( k6_relat_1 @ sk_B ) )
    = ( k9_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup+',[status(thm)],['7','17'])).

thf('19',plain,(
    ! [X11: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('20',plain,
    ( sk_B
    = ( k9_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t159_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k9_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k9_relat_1 @ C @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('21',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k9_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k9_relat_1 @ X7 @ ( k9_relat_1 @ X8 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t159_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ X0 ) @ sk_B )
        = ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ X0 ) @ sk_B )
        = ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k7_relat_1 @ X0 @ sk_C ) @ sk_B )
        = ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X0 @ sk_C ) @ sk_B )
        = ( k9_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ( k9_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B )
 != ( k9_relat_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( ( k9_relat_1 @ sk_A @ sk_B )
     != ( k9_relat_1 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ( k9_relat_1 @ sk_A @ sk_B )
 != ( k9_relat_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    $false ),
    inference(simplify,[status(thm)],['30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rsrpG6mR47
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:57:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 24 iterations in 0.022s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.20/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.47  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.47  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.47  thf(t94_relat_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ B ) =>
% 0.20/0.47       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      (![X12 : $i, X13 : $i]:
% 0.20/0.47         (((k7_relat_1 @ X13 @ X12) = (k5_relat_1 @ (k6_relat_1 @ X12) @ X13))
% 0.20/0.47          | ~ (v1_relat_1 @ X13))),
% 0.20/0.47      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.20/0.47  thf(t162_relat_1, conjecture,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ A ) =>
% 0.20/0.47       ( ![B:$i,C:$i]:
% 0.20/0.47         ( ( r1_tarski @ B @ C ) =>
% 0.20/0.47           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 0.20/0.47             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i]:
% 0.20/0.47        ( ( v1_relat_1 @ A ) =>
% 0.20/0.47          ( ![B:$i,C:$i]:
% 0.20/0.47            ( ( r1_tarski @ B @ C ) =>
% 0.20/0.47              ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 0.20/0.47                ( k9_relat_1 @ A @ B ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t162_relat_1])).
% 0.20/0.47  thf('1', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t71_relat_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.20/0.47       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.47  thf('2', plain, (![X11 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 0.20/0.47      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.47  thf(t125_relat_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ B ) =>
% 0.20/0.47       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.20/0.47         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i]:
% 0.20/0.47         (~ (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 0.20/0.47          | ((k8_relat_1 @ X4 @ X3) = (X3))
% 0.20/0.47          | ~ (v1_relat_1 @ X3))),
% 0.20/0.47      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.47          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.20/0.47          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.47  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.20/0.47  thf('5', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.47          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 0.20/0.47      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (((k8_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) = (k6_relat_1 @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '6'])).
% 0.20/0.47  thf(t123_relat_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ B ) =>
% 0.20/0.47       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X1 : $i, X2 : $i]:
% 0.20/0.47         (((k8_relat_1 @ X2 @ X1) = (k5_relat_1 @ X1 @ (k6_relat_1 @ X2)))
% 0.20/0.47          | ~ (v1_relat_1 @ X1))),
% 0.20/0.47      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X12 : $i, X13 : $i]:
% 0.20/0.47         (((k7_relat_1 @ X13 @ X12) = (k5_relat_1 @ (k6_relat_1 @ X12) @ X13))
% 0.20/0.47          | ~ (v1_relat_1 @ X13))),
% 0.20/0.47      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.20/0.47            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.20/0.47          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.20/0.47          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.20/0.47      inference('sup+', [status(thm)], ['8', '9'])).
% 0.20/0.47  thf('11', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.47  thf('12', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.20/0.47           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.20/0.47      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.20/0.47  thf(t148_relat_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ B ) =>
% 0.20/0.47       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X5 : $i, X6 : $i]:
% 0.20/0.47         (((k2_relat_1 @ (k7_relat_1 @ X5 @ X6)) = (k9_relat_1 @ X5 @ X6))
% 0.20/0.47          | ~ (v1_relat_1 @ X5))),
% 0.20/0.47      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.20/0.47            = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.20/0.47          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.20/0.47      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.47  thf('16', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.20/0.47           = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.20/0.47      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      (((k2_relat_1 @ (k6_relat_1 @ sk_B))
% 0.20/0.47         = (k9_relat_1 @ (k6_relat_1 @ sk_C) @ sk_B))),
% 0.20/0.47      inference('sup+', [status(thm)], ['7', '17'])).
% 0.20/0.47  thf('19', plain, (![X11 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 0.20/0.47      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.47  thf('20', plain, (((sk_B) = (k9_relat_1 @ (k6_relat_1 @ sk_C) @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.47  thf(t159_relat_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ B ) =>
% 0.20/0.47       ( ![C:$i]:
% 0.20/0.47         ( ( v1_relat_1 @ C ) =>
% 0.20/0.47           ( ( k9_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.20/0.47             ( k9_relat_1 @ C @ ( k9_relat_1 @ B @ A ) ) ) ) ) ))).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X7)
% 0.20/0.47          | ((k9_relat_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 0.20/0.47              = (k9_relat_1 @ X7 @ (k9_relat_1 @ X8 @ X9)))
% 0.20/0.47          | ~ (v1_relat_1 @ X8))),
% 0.20/0.47      inference('cnf', [status(esa)], [t159_relat_1])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((k9_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_C) @ X0) @ sk_B)
% 0.20/0.47            = (k9_relat_1 @ X0 @ sk_B))
% 0.20/0.47          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_C))
% 0.20/0.47          | ~ (v1_relat_1 @ X0))),
% 0.20/0.47      inference('sup+', [status(thm)], ['20', '21'])).
% 0.20/0.47  thf('23', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.47  thf('24', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((k9_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_C) @ X0) @ sk_B)
% 0.20/0.47            = (k9_relat_1 @ X0 @ sk_B))
% 0.20/0.47          | ~ (v1_relat_1 @ X0))),
% 0.20/0.47      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.47  thf('25', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((k9_relat_1 @ (k7_relat_1 @ X0 @ sk_C) @ sk_B)
% 0.20/0.47            = (k9_relat_1 @ X0 @ sk_B))
% 0.20/0.47          | ~ (v1_relat_1 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ X0))),
% 0.20/0.47      inference('sup+', [status(thm)], ['0', '24'])).
% 0.20/0.47  thf('26', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X0)
% 0.20/0.47          | ((k9_relat_1 @ (k7_relat_1 @ X0 @ sk_C) @ sk_B)
% 0.20/0.47              = (k9_relat_1 @ X0 @ sk_B)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      (((k9_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B)
% 0.20/0.47         != (k9_relat_1 @ sk_A @ sk_B))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('28', plain,
% 0.20/0.47      ((((k9_relat_1 @ sk_A @ sk_B) != (k9_relat_1 @ sk_A @ sk_B))
% 0.20/0.47        | ~ (v1_relat_1 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.47  thf('29', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('30', plain,
% 0.20/0.47      (((k9_relat_1 @ sk_A @ sk_B) != (k9_relat_1 @ sk_A @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.47  thf('31', plain, ($false), inference('simplify', [status(thm)], ['30'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
