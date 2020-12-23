%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.069QYU8EZQ

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   42 (  52 expanded)
%              Number of leaves         :   17 (  22 expanded)
%              Depth                    :   14
%              Number of atoms          :  286 ( 486 expanded)
%              Number of equality atoms :   17 (  27 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k7_relat_1 @ X12 @ X11 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X11 ) @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) ) @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

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

thf('2',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['5','6'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ( ( k5_relat_1 @ X7 @ ( k6_relat_1 @ X8 ) )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['9','10'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X5 @ X4 ) @ X6 )
        = ( k5_relat_1 @ X5 @ ( k5_relat_1 @ X4 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('15',plain,(
    ! [X3: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ ( k7_relat_1 @ X0 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ ( k7_relat_1 @ X0 @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ( k5_relat_1 @ sk_B @ ( k7_relat_1 @ sk_C @ sk_A ) )
 != ( k5_relat_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( k5_relat_1 @ sk_B @ sk_C )
     != ( k5_relat_1 @ sk_B @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ( k5_relat_1 @ sk_B @ sk_C )
 != ( k5_relat_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    $false ),
    inference(simplify,[status(thm)],['22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.069QYU8EZQ
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:53:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 39 iterations in 0.039s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.49  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.49  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.49  thf(t94_relat_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ B ) =>
% 0.21/0.49       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (![X11 : $i, X12 : $i]:
% 0.21/0.49         (((k7_relat_1 @ X12 @ X11) = (k5_relat_1 @ (k6_relat_1 @ X11) @ X12))
% 0.21/0.49          | ~ (v1_relat_1 @ X12))),
% 0.21/0.49      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.21/0.49  thf(t87_relat_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ B ) =>
% 0.21/0.49       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i]:
% 0.21/0.49         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X9 @ X10)) @ X10)
% 0.21/0.49          | ~ (v1_relat_1 @ X9))),
% 0.21/0.49      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.21/0.49  thf(t200_relat_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ B ) =>
% 0.21/0.49       ( ![C:$i]:
% 0.21/0.49         ( ( v1_relat_1 @ C ) =>
% 0.21/0.49           ( ( r1_tarski @
% 0.21/0.49               ( k2_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ C @ A ) ) ) =>
% 0.21/0.49             ( ( k5_relat_1 @ B @ ( k7_relat_1 @ C @ A ) ) =
% 0.21/0.49               ( k5_relat_1 @ B @ C ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i]:
% 0.21/0.49        ( ( v1_relat_1 @ B ) =>
% 0.21/0.49          ( ![C:$i]:
% 0.21/0.49            ( ( v1_relat_1 @ C ) =>
% 0.21/0.49              ( ( r1_tarski @
% 0.21/0.49                  ( k2_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ C @ A ) ) ) =>
% 0.21/0.49                ( ( k5_relat_1 @ B @ ( k7_relat_1 @ C @ A ) ) =
% 0.21/0.49                  ( k5_relat_1 @ B @ C ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t200_relat_1])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      ((r1_tarski @ (k2_relat_1 @ sk_B) @ 
% 0.21/0.49        (k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t1_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.49       ( r1_tarski @ A @ C ) ))).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.49          | ~ (r1_tarski @ X1 @ X2)
% 0.21/0.49          | (r1_tarski @ X0 @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r1_tarski @ (k2_relat_1 @ sk_B) @ X0)
% 0.21/0.49          | ~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)) @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_B) @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '4'])).
% 0.21/0.49  thf('6', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('7', plain, ((r1_tarski @ (k2_relat_1 @ sk_B) @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['5', '6'])).
% 0.21/0.49  thf(t79_relat_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ B ) =>
% 0.21/0.49       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.21/0.49         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i]:
% 0.21/0.49         (~ (r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 0.21/0.49          | ((k5_relat_1 @ X7 @ (k6_relat_1 @ X8)) = (X7))
% 0.21/0.49          | ~ (v1_relat_1 @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.49        | ((k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)) = (sk_B)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf('10', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('11', plain, (((k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)) = (sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.49  thf(t55_relat_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( v1_relat_1 @ B ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( v1_relat_1 @ C ) =>
% 0.21/0.49               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.21/0.49                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X4)
% 0.21/0.49          | ((k5_relat_1 @ (k5_relat_1 @ X5 @ X4) @ X6)
% 0.21/0.49              = (k5_relat_1 @ X5 @ (k5_relat_1 @ X4 @ X6)))
% 0.21/0.49          | ~ (v1_relat_1 @ X6)
% 0.21/0.49          | ~ (v1_relat_1 @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k5_relat_1 @ sk_B @ X0)
% 0.21/0.49            = (k5_relat_1 @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ X0)))
% 0.21/0.49          | ~ (v1_relat_1 @ sk_B)
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf('14', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.21/0.49  thf('15', plain, (![X3 : $i]: (v1_relat_1 @ (k6_relat_1 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k5_relat_1 @ sk_B @ X0)
% 0.21/0.49            = (k5_relat_1 @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ X0)))
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k5_relat_1 @ sk_B @ X0)
% 0.21/0.49            = (k5_relat_1 @ sk_B @ (k7_relat_1 @ X0 @ sk_A)))
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['0', '16'])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X0)
% 0.21/0.49          | ((k5_relat_1 @ sk_B @ X0)
% 0.21/0.49              = (k5_relat_1 @ sk_B @ (k7_relat_1 @ X0 @ sk_A))))),
% 0.21/0.49      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (((k5_relat_1 @ sk_B @ (k7_relat_1 @ sk_C @ sk_A))
% 0.21/0.49         != (k5_relat_1 @ sk_B @ sk_C))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      ((((k5_relat_1 @ sk_B @ sk_C) != (k5_relat_1 @ sk_B @ sk_C))
% 0.21/0.49        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.49  thf('21', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (((k5_relat_1 @ sk_B @ sk_C) != (k5_relat_1 @ sk_B @ sk_C))),
% 0.21/0.49      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.49  thf('23', plain, ($false), inference('simplify', [status(thm)], ['22'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
