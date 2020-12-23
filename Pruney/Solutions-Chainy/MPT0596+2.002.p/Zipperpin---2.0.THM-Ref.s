%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2SVH7FMFQc

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:38 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   53 (  65 expanded)
%              Number of leaves         :   21 (  28 expanded)
%              Depth                    :   12
%              Number of atoms          :  403 ( 621 expanded)
%              Number of equality atoms :   20 (  30 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

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
    ! [X5: $i,X6: $i] :
      ( ( ( k8_relat_1 @ X6 @ X5 )
        = ( k5_relat_1 @ X5 @ ( k6_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) @ X11 )
        = ( k5_relat_1 @ X10 @ ( k5_relat_1 @ X9 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
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
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X4 ) ) ),
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
    ( k5_relat_1 @ sk_B @ ( k7_relat_1 @ sk_C_1 @ sk_A ) )
 != ( k5_relat_1 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k5_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) @ sk_C_1 )
     != ( k5_relat_1 @ sk_B @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C_1 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf(t86_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('16',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ ( k7_relat_1 @ X14 @ X13 ) ) )
      | ( r2_hidden @ X12 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ sk_A )
    | ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B ) @ sk_A ),
    inference(simplify,[status(thm)],['21'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('23',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ( ( k8_relat_1 @ X8 @ X7 )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k8_relat_1 @ sk_A @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k8_relat_1 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ( k5_relat_1 @ sk_B @ sk_C_1 )
 != ( k5_relat_1 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['10','26','27','28'])).

thf('30',plain,(
    $false ),
    inference(simplify,[status(thm)],['29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2SVH7FMFQc
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:47:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.75/0.95  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.75/0.95  % Solved by: fo/fo7.sh
% 0.75/0.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.95  % done 433 iterations in 0.504s
% 0.75/0.95  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.75/0.95  % SZS output start Refutation
% 0.75/0.95  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.75/0.95  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.75/0.95  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.75/0.95  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.75/0.95  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.95  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.75/0.95  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.75/0.95  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.75/0.95  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.95  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/0.95  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.75/0.95  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.75/0.95  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.75/0.95  thf(t94_relat_1, axiom,
% 0.75/0.95    (![A:$i,B:$i]:
% 0.75/0.95     ( ( v1_relat_1 @ B ) =>
% 0.75/0.95       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.75/0.95  thf('0', plain,
% 0.75/0.95      (![X15 : $i, X16 : $i]:
% 0.75/0.95         (((k7_relat_1 @ X16 @ X15) = (k5_relat_1 @ (k6_relat_1 @ X15) @ X16))
% 0.75/0.95          | ~ (v1_relat_1 @ X16))),
% 0.75/0.95      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.75/0.95  thf(t123_relat_1, axiom,
% 0.75/0.95    (![A:$i,B:$i]:
% 0.75/0.95     ( ( v1_relat_1 @ B ) =>
% 0.75/0.95       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.75/0.95  thf('1', plain,
% 0.75/0.95      (![X5 : $i, X6 : $i]:
% 0.75/0.95         (((k8_relat_1 @ X6 @ X5) = (k5_relat_1 @ X5 @ (k6_relat_1 @ X6)))
% 0.75/0.95          | ~ (v1_relat_1 @ X5))),
% 0.75/0.95      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.75/0.95  thf(t55_relat_1, axiom,
% 0.75/0.95    (![A:$i]:
% 0.75/0.95     ( ( v1_relat_1 @ A ) =>
% 0.75/0.95       ( ![B:$i]:
% 0.75/0.95         ( ( v1_relat_1 @ B ) =>
% 0.75/0.95           ( ![C:$i]:
% 0.75/0.95             ( ( v1_relat_1 @ C ) =>
% 0.75/0.95               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.75/0.95                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.75/0.95  thf('2', plain,
% 0.75/0.95      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.75/0.95         (~ (v1_relat_1 @ X9)
% 0.75/0.95          | ((k5_relat_1 @ (k5_relat_1 @ X10 @ X9) @ X11)
% 0.75/0.95              = (k5_relat_1 @ X10 @ (k5_relat_1 @ X9 @ X11)))
% 0.75/0.95          | ~ (v1_relat_1 @ X11)
% 0.75/0.95          | ~ (v1_relat_1 @ X10))),
% 0.75/0.95      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.75/0.95  thf('3', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.95         (((k5_relat_1 @ (k8_relat_1 @ X1 @ X0) @ X2)
% 0.75/0.95            = (k5_relat_1 @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X2)))
% 0.75/0.95          | ~ (v1_relat_1 @ X0)
% 0.75/0.95          | ~ (v1_relat_1 @ X0)
% 0.75/0.95          | ~ (v1_relat_1 @ X2)
% 0.75/0.95          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.75/0.95      inference('sup+', [status(thm)], ['1', '2'])).
% 0.75/0.95  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.75/0.95  thf('4', plain, (![X4 : $i]: (v1_relat_1 @ (k6_relat_1 @ X4))),
% 0.75/0.95      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.75/0.95  thf('5', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.95         (((k5_relat_1 @ (k8_relat_1 @ X1 @ X0) @ X2)
% 0.75/0.95            = (k5_relat_1 @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X2)))
% 0.75/0.95          | ~ (v1_relat_1 @ X0)
% 0.75/0.95          | ~ (v1_relat_1 @ X0)
% 0.75/0.95          | ~ (v1_relat_1 @ X2))),
% 0.75/0.95      inference('demod', [status(thm)], ['3', '4'])).
% 0.75/0.95  thf('6', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.95         (~ (v1_relat_1 @ X2)
% 0.75/0.95          | ~ (v1_relat_1 @ X0)
% 0.75/0.95          | ((k5_relat_1 @ (k8_relat_1 @ X1 @ X0) @ X2)
% 0.75/0.95              = (k5_relat_1 @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X2))))),
% 0.75/0.95      inference('simplify', [status(thm)], ['5'])).
% 0.75/0.95  thf('7', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.95         (((k5_relat_1 @ (k8_relat_1 @ X0 @ X2) @ X1)
% 0.75/0.95            = (k5_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0)))
% 0.75/0.95          | ~ (v1_relat_1 @ X1)
% 0.75/0.95          | ~ (v1_relat_1 @ X2)
% 0.75/0.95          | ~ (v1_relat_1 @ X1))),
% 0.75/0.95      inference('sup+', [status(thm)], ['0', '6'])).
% 0.75/0.95  thf('8', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.95         (~ (v1_relat_1 @ X2)
% 0.75/0.95          | ~ (v1_relat_1 @ X1)
% 0.75/0.95          | ((k5_relat_1 @ (k8_relat_1 @ X0 @ X2) @ X1)
% 0.75/0.95              = (k5_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0))))),
% 0.75/0.95      inference('simplify', [status(thm)], ['7'])).
% 0.75/0.95  thf(t200_relat_1, conjecture,
% 0.75/0.95    (![A:$i,B:$i]:
% 0.75/0.95     ( ( v1_relat_1 @ B ) =>
% 0.75/0.95       ( ![C:$i]:
% 0.75/0.95         ( ( v1_relat_1 @ C ) =>
% 0.75/0.95           ( ( r1_tarski @
% 0.75/0.95               ( k2_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ C @ A ) ) ) =>
% 0.75/0.95             ( ( k5_relat_1 @ B @ ( k7_relat_1 @ C @ A ) ) =
% 0.75/0.95               ( k5_relat_1 @ B @ C ) ) ) ) ) ))).
% 0.75/0.95  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.95    (~( ![A:$i,B:$i]:
% 0.75/0.95        ( ( v1_relat_1 @ B ) =>
% 0.75/0.95          ( ![C:$i]:
% 0.75/0.95            ( ( v1_relat_1 @ C ) =>
% 0.75/0.95              ( ( r1_tarski @
% 0.75/0.95                  ( k2_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ C @ A ) ) ) =>
% 0.75/0.95                ( ( k5_relat_1 @ B @ ( k7_relat_1 @ C @ A ) ) =
% 0.75/0.95                  ( k5_relat_1 @ B @ C ) ) ) ) ) ) )),
% 0.75/0.95    inference('cnf.neg', [status(esa)], [t200_relat_1])).
% 0.75/0.95  thf('9', plain,
% 0.75/0.95      (((k5_relat_1 @ sk_B @ (k7_relat_1 @ sk_C_1 @ sk_A))
% 0.75/0.95         != (k5_relat_1 @ sk_B @ sk_C_1))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('10', plain,
% 0.75/0.95      ((((k5_relat_1 @ (k8_relat_1 @ sk_A @ sk_B) @ sk_C_1)
% 0.75/0.95          != (k5_relat_1 @ sk_B @ sk_C_1))
% 0.75/0.95        | ~ (v1_relat_1 @ sk_C_1)
% 0.75/0.95        | ~ (v1_relat_1 @ sk_B))),
% 0.75/0.95      inference('sup-', [status(thm)], ['8', '9'])).
% 0.75/0.95  thf(d3_tarski, axiom,
% 0.75/0.95    (![A:$i,B:$i]:
% 0.75/0.95     ( ( r1_tarski @ A @ B ) <=>
% 0.75/0.95       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.75/0.95  thf('11', plain,
% 0.75/0.95      (![X1 : $i, X3 : $i]:
% 0.75/0.95         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.75/0.95      inference('cnf', [status(esa)], [d3_tarski])).
% 0.75/0.95  thf('12', plain,
% 0.75/0.95      ((r1_tarski @ (k2_relat_1 @ sk_B) @ 
% 0.75/0.95        (k1_relat_1 @ (k7_relat_1 @ sk_C_1 @ sk_A)))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('13', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.95         (~ (r2_hidden @ X0 @ X1)
% 0.75/0.95          | (r2_hidden @ X0 @ X2)
% 0.75/0.95          | ~ (r1_tarski @ X1 @ X2))),
% 0.75/0.95      inference('cnf', [status(esa)], [d3_tarski])).
% 0.75/0.95  thf('14', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         ((r2_hidden @ X0 @ (k1_relat_1 @ (k7_relat_1 @ sk_C_1 @ sk_A)))
% 0.75/0.95          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['12', '13'])).
% 0.75/0.95  thf('15', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         ((r1_tarski @ (k2_relat_1 @ sk_B) @ X0)
% 0.75/0.95          | (r2_hidden @ (sk_C @ X0 @ (k2_relat_1 @ sk_B)) @ 
% 0.75/0.95             (k1_relat_1 @ (k7_relat_1 @ sk_C_1 @ sk_A))))),
% 0.75/0.95      inference('sup-', [status(thm)], ['11', '14'])).
% 0.75/0.95  thf(t86_relat_1, axiom,
% 0.75/0.95    (![A:$i,B:$i,C:$i]:
% 0.75/0.95     ( ( v1_relat_1 @ C ) =>
% 0.75/0.95       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) <=>
% 0.75/0.95         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ))).
% 0.75/0.95  thf('16', plain,
% 0.75/0.95      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.75/0.95         (~ (r2_hidden @ X12 @ (k1_relat_1 @ (k7_relat_1 @ X14 @ X13)))
% 0.75/0.95          | (r2_hidden @ X12 @ X13)
% 0.75/0.95          | ~ (v1_relat_1 @ X14))),
% 0.75/0.95      inference('cnf', [status(esa)], [t86_relat_1])).
% 0.75/0.95  thf('17', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         ((r1_tarski @ (k2_relat_1 @ sk_B) @ X0)
% 0.75/0.95          | ~ (v1_relat_1 @ sk_C_1)
% 0.75/0.95          | (r2_hidden @ (sk_C @ X0 @ (k2_relat_1 @ sk_B)) @ sk_A))),
% 0.75/0.95      inference('sup-', [status(thm)], ['15', '16'])).
% 0.75/0.95  thf('18', plain, ((v1_relat_1 @ sk_C_1)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('19', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         ((r1_tarski @ (k2_relat_1 @ sk_B) @ X0)
% 0.75/0.95          | (r2_hidden @ (sk_C @ X0 @ (k2_relat_1 @ sk_B)) @ sk_A))),
% 0.75/0.95      inference('demod', [status(thm)], ['17', '18'])).
% 0.75/0.95  thf('20', plain,
% 0.75/0.95      (![X1 : $i, X3 : $i]:
% 0.75/0.95         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.75/0.95      inference('cnf', [status(esa)], [d3_tarski])).
% 0.75/0.95  thf('21', plain,
% 0.75/0.95      (((r1_tarski @ (k2_relat_1 @ sk_B) @ sk_A)
% 0.75/0.95        | (r1_tarski @ (k2_relat_1 @ sk_B) @ sk_A))),
% 0.75/0.95      inference('sup-', [status(thm)], ['19', '20'])).
% 0.75/0.95  thf('22', plain, ((r1_tarski @ (k2_relat_1 @ sk_B) @ sk_A)),
% 0.75/0.95      inference('simplify', [status(thm)], ['21'])).
% 0.75/0.95  thf(t125_relat_1, axiom,
% 0.75/0.95    (![A:$i,B:$i]:
% 0.75/0.95     ( ( v1_relat_1 @ B ) =>
% 0.75/0.95       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.75/0.95         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.75/0.95  thf('23', plain,
% 0.75/0.95      (![X7 : $i, X8 : $i]:
% 0.75/0.95         (~ (r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 0.75/0.95          | ((k8_relat_1 @ X8 @ X7) = (X7))
% 0.75/0.95          | ~ (v1_relat_1 @ X7))),
% 0.75/0.95      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.75/0.95  thf('24', plain,
% 0.75/0.95      ((~ (v1_relat_1 @ sk_B) | ((k8_relat_1 @ sk_A @ sk_B) = (sk_B)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['22', '23'])).
% 0.75/0.95  thf('25', plain, ((v1_relat_1 @ sk_B)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('26', plain, (((k8_relat_1 @ sk_A @ sk_B) = (sk_B))),
% 0.75/0.95      inference('demod', [status(thm)], ['24', '25'])).
% 0.75/0.95  thf('27', plain, ((v1_relat_1 @ sk_C_1)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('28', plain, ((v1_relat_1 @ sk_B)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('29', plain,
% 0.75/0.95      (((k5_relat_1 @ sk_B @ sk_C_1) != (k5_relat_1 @ sk_B @ sk_C_1))),
% 0.75/0.95      inference('demod', [status(thm)], ['10', '26', '27', '28'])).
% 0.75/0.95  thf('30', plain, ($false), inference('simplify', [status(thm)], ['29'])).
% 0.75/0.95  
% 0.75/0.95  % SZS output end Refutation
% 0.75/0.95  
% 0.75/0.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
