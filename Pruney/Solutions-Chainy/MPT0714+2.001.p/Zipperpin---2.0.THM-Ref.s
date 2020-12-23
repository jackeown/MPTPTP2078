%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.h1gqx8yeNI

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:18 EST 2020

% Result     : Theorem 2.23s
% Output     : Refutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   49 (  57 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :   16
%              Number of atoms          :  444 ( 628 expanded)
%              Number of equality atoms :   28 (  36 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t112_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) @ X7 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X6 @ X7 ) @ X5 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t112_relat_1])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X8 @ X9 ) )
        = ( k9_relat_1 @ X8 @ X9 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k7_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X15 ) @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ( ( k5_relat_1 @ X13 @ ( k6_relat_1 @ X14 ) )
        = X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) @ X12 )
        = ( k5_relat_1 @ X11 @ ( k5_relat_1 @ X10 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k7_relat_1 @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k7_relat_1 @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['1','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k7_relat_1 @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t169_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ! [C: $i] :
              ( ( k5_relat_1 @ ( k7_relat_1 @ A @ C ) @ ( k7_relat_1 @ B @ ( k9_relat_1 @ A @ C ) ) )
              = ( k7_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ! [C: $i] :
                ( ( k5_relat_1 @ ( k7_relat_1 @ A @ C ) @ ( k7_relat_1 @ B @ ( k9_relat_1 @ A @ C ) ) )
                = ( k7_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t169_funct_1])).

thf('18',plain,(
    ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ ( k7_relat_1 @ sk_B @ ( k9_relat_1 @ sk_A @ sk_C ) ) )
 != ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B )
     != ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B )
 != ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ( ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C )
     != ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C )
 != ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    $false ),
    inference(simplify,[status(thm)],['26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.h1gqx8yeNI
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:00:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.23/2.42  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.23/2.42  % Solved by: fo/fo7.sh
% 2.23/2.42  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.23/2.42  % done 1824 iterations in 1.963s
% 2.23/2.42  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.23/2.42  % SZS output start Refutation
% 2.23/2.42  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 2.23/2.42  thf(sk_B_type, type, sk_B: $i).
% 2.23/2.42  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.23/2.42  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.23/2.42  thf(sk_A_type, type, sk_A: $i).
% 2.23/2.42  thf(sk_C_type, type, sk_C: $i).
% 2.23/2.42  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.23/2.42  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.23/2.42  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.23/2.42  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 2.23/2.42  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.23/2.42  thf(t112_relat_1, axiom,
% 2.23/2.42    (![A:$i,B:$i]:
% 2.23/2.42     ( ( v1_relat_1 @ B ) =>
% 2.23/2.42       ( ![C:$i]:
% 2.23/2.42         ( ( v1_relat_1 @ C ) =>
% 2.23/2.42           ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 2.23/2.42             ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) ))).
% 2.23/2.42  thf('0', plain,
% 2.23/2.42      (![X5 : $i, X6 : $i, X7 : $i]:
% 2.23/2.42         (~ (v1_relat_1 @ X5)
% 2.23/2.42          | ((k7_relat_1 @ (k5_relat_1 @ X6 @ X5) @ X7)
% 2.23/2.42              = (k5_relat_1 @ (k7_relat_1 @ X6 @ X7) @ X5))
% 2.23/2.42          | ~ (v1_relat_1 @ X6))),
% 2.23/2.42      inference('cnf', [status(esa)], [t112_relat_1])).
% 2.23/2.42  thf(dt_k7_relat_1, axiom,
% 2.23/2.42    (![A:$i,B:$i]:
% 2.23/2.42     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 2.23/2.42  thf('1', plain,
% 2.23/2.42      (![X3 : $i, X4 : $i]:
% 2.23/2.42         (~ (v1_relat_1 @ X3) | (v1_relat_1 @ (k7_relat_1 @ X3 @ X4)))),
% 2.23/2.42      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 2.23/2.42  thf(t148_relat_1, axiom,
% 2.23/2.42    (![A:$i,B:$i]:
% 2.23/2.42     ( ( v1_relat_1 @ B ) =>
% 2.23/2.42       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 2.23/2.42  thf('2', plain,
% 2.23/2.42      (![X8 : $i, X9 : $i]:
% 2.23/2.42         (((k2_relat_1 @ (k7_relat_1 @ X8 @ X9)) = (k9_relat_1 @ X8 @ X9))
% 2.23/2.42          | ~ (v1_relat_1 @ X8))),
% 2.23/2.42      inference('cnf', [status(esa)], [t148_relat_1])).
% 2.23/2.42  thf(t94_relat_1, axiom,
% 2.23/2.42    (![A:$i,B:$i]:
% 2.23/2.42     ( ( v1_relat_1 @ B ) =>
% 2.23/2.42       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 2.23/2.42  thf('3', plain,
% 2.23/2.42      (![X15 : $i, X16 : $i]:
% 2.23/2.42         (((k7_relat_1 @ X16 @ X15) = (k5_relat_1 @ (k6_relat_1 @ X15) @ X16))
% 2.23/2.42          | ~ (v1_relat_1 @ X16))),
% 2.23/2.42      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.23/2.42  thf(d10_xboole_0, axiom,
% 2.23/2.42    (![A:$i,B:$i]:
% 2.23/2.42     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.23/2.42  thf('4', plain,
% 2.23/2.42      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 2.23/2.42      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.23/2.42  thf('5', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.23/2.42      inference('simplify', [status(thm)], ['4'])).
% 2.23/2.42  thf(t79_relat_1, axiom,
% 2.23/2.42    (![A:$i,B:$i]:
% 2.23/2.42     ( ( v1_relat_1 @ B ) =>
% 2.23/2.42       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 2.23/2.42         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 2.23/2.42  thf('6', plain,
% 2.23/2.42      (![X13 : $i, X14 : $i]:
% 2.23/2.42         (~ (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 2.23/2.42          | ((k5_relat_1 @ X13 @ (k6_relat_1 @ X14)) = (X13))
% 2.23/2.42          | ~ (v1_relat_1 @ X13))),
% 2.23/2.42      inference('cnf', [status(esa)], [t79_relat_1])).
% 2.23/2.42  thf('7', plain,
% 2.23/2.42      (![X0 : $i]:
% 2.23/2.42         (~ (v1_relat_1 @ X0)
% 2.23/2.42          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0))) = (X0)))),
% 2.23/2.42      inference('sup-', [status(thm)], ['5', '6'])).
% 2.23/2.42  thf(t55_relat_1, axiom,
% 2.23/2.42    (![A:$i]:
% 2.23/2.42     ( ( v1_relat_1 @ A ) =>
% 2.23/2.42       ( ![B:$i]:
% 2.23/2.42         ( ( v1_relat_1 @ B ) =>
% 2.23/2.42           ( ![C:$i]:
% 2.23/2.42             ( ( v1_relat_1 @ C ) =>
% 2.23/2.42               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 2.23/2.42                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 2.23/2.42  thf('8', plain,
% 2.23/2.42      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.23/2.42         (~ (v1_relat_1 @ X10)
% 2.23/2.42          | ((k5_relat_1 @ (k5_relat_1 @ X11 @ X10) @ X12)
% 2.23/2.42              = (k5_relat_1 @ X11 @ (k5_relat_1 @ X10 @ X12)))
% 2.23/2.42          | ~ (v1_relat_1 @ X12)
% 2.23/2.42          | ~ (v1_relat_1 @ X11))),
% 2.23/2.42      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.23/2.42  thf('9', plain,
% 2.23/2.42      (![X0 : $i, X1 : $i]:
% 2.23/2.42         (((k5_relat_1 @ X0 @ X1)
% 2.23/2.42            = (k5_relat_1 @ X0 @ 
% 2.23/2.42               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1)))
% 2.23/2.42          | ~ (v1_relat_1 @ X0)
% 2.23/2.42          | ~ (v1_relat_1 @ X0)
% 2.23/2.42          | ~ (v1_relat_1 @ X1)
% 2.23/2.42          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))),
% 2.23/2.42      inference('sup+', [status(thm)], ['7', '8'])).
% 2.23/2.42  thf(fc3_funct_1, axiom,
% 2.23/2.42    (![A:$i]:
% 2.23/2.42     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 2.23/2.42       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 2.23/2.42  thf('10', plain, (![X17 : $i]: (v1_relat_1 @ (k6_relat_1 @ X17))),
% 2.23/2.42      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.23/2.42  thf('11', plain,
% 2.23/2.42      (![X0 : $i, X1 : $i]:
% 2.23/2.42         (((k5_relat_1 @ X0 @ X1)
% 2.23/2.42            = (k5_relat_1 @ X0 @ 
% 2.23/2.42               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1)))
% 2.23/2.42          | ~ (v1_relat_1 @ X0)
% 2.23/2.42          | ~ (v1_relat_1 @ X0)
% 2.23/2.42          | ~ (v1_relat_1 @ X1))),
% 2.23/2.42      inference('demod', [status(thm)], ['9', '10'])).
% 2.23/2.42  thf('12', plain,
% 2.23/2.42      (![X0 : $i, X1 : $i]:
% 2.23/2.42         (~ (v1_relat_1 @ X1)
% 2.23/2.42          | ~ (v1_relat_1 @ X0)
% 2.23/2.42          | ((k5_relat_1 @ X0 @ X1)
% 2.23/2.42              = (k5_relat_1 @ X0 @ 
% 2.23/2.42                 (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1))))),
% 2.23/2.42      inference('simplify', [status(thm)], ['11'])).
% 2.23/2.42  thf('13', plain,
% 2.23/2.42      (![X0 : $i, X1 : $i]:
% 2.23/2.42         (((k5_relat_1 @ X0 @ X1)
% 2.23/2.42            = (k5_relat_1 @ X0 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0))))
% 2.23/2.42          | ~ (v1_relat_1 @ X1)
% 2.23/2.42          | ~ (v1_relat_1 @ X0)
% 2.23/2.42          | ~ (v1_relat_1 @ X1))),
% 2.23/2.42      inference('sup+', [status(thm)], ['3', '12'])).
% 2.23/2.42  thf('14', plain,
% 2.23/2.42      (![X0 : $i, X1 : $i]:
% 2.23/2.42         (~ (v1_relat_1 @ X0)
% 2.23/2.42          | ~ (v1_relat_1 @ X1)
% 2.23/2.42          | ((k5_relat_1 @ X0 @ X1)
% 2.23/2.42              = (k5_relat_1 @ X0 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0)))))),
% 2.23/2.42      inference('simplify', [status(thm)], ['13'])).
% 2.23/2.42  thf('15', plain,
% 2.23/2.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.23/2.42         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 2.23/2.42            = (k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 2.23/2.42               (k7_relat_1 @ X2 @ (k9_relat_1 @ X1 @ X0))))
% 2.23/2.42          | ~ (v1_relat_1 @ X1)
% 2.23/2.42          | ~ (v1_relat_1 @ X2)
% 2.23/2.42          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 2.23/2.42      inference('sup+', [status(thm)], ['2', '14'])).
% 2.23/2.42  thf('16', plain,
% 2.23/2.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.23/2.42         (~ (v1_relat_1 @ X1)
% 2.23/2.42          | ~ (v1_relat_1 @ X2)
% 2.23/2.42          | ~ (v1_relat_1 @ X1)
% 2.23/2.42          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 2.23/2.42              = (k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 2.23/2.42                 (k7_relat_1 @ X2 @ (k9_relat_1 @ X1 @ X0)))))),
% 2.23/2.42      inference('sup-', [status(thm)], ['1', '15'])).
% 2.23/2.42  thf('17', plain,
% 2.23/2.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.23/2.42         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 2.23/2.42            = (k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 2.23/2.42               (k7_relat_1 @ X2 @ (k9_relat_1 @ X1 @ X0))))
% 2.23/2.42          | ~ (v1_relat_1 @ X2)
% 2.23/2.42          | ~ (v1_relat_1 @ X1))),
% 2.23/2.42      inference('simplify', [status(thm)], ['16'])).
% 2.23/2.42  thf(t169_funct_1, conjecture,
% 2.23/2.42    (![A:$i]:
% 2.23/2.42     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.23/2.42       ( ![B:$i]:
% 2.23/2.42         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.23/2.42           ( ![C:$i]:
% 2.23/2.42             ( ( k5_relat_1 @
% 2.23/2.42                 ( k7_relat_1 @ A @ C ) @ 
% 2.23/2.42                 ( k7_relat_1 @ B @ ( k9_relat_1 @ A @ C ) ) ) =
% 2.23/2.42               ( k7_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) ) ) ) ) ))).
% 2.23/2.42  thf(zf_stmt_0, negated_conjecture,
% 2.23/2.42    (~( ![A:$i]:
% 2.23/2.42        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.23/2.42          ( ![B:$i]:
% 2.23/2.42            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.23/2.42              ( ![C:$i]:
% 2.23/2.42                ( ( k5_relat_1 @
% 2.23/2.42                    ( k7_relat_1 @ A @ C ) @ 
% 2.23/2.42                    ( k7_relat_1 @ B @ ( k9_relat_1 @ A @ C ) ) ) =
% 2.23/2.42                  ( k7_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) ) ) ) ) ) )),
% 2.23/2.42    inference('cnf.neg', [status(esa)], [t169_funct_1])).
% 2.23/2.42  thf('18', plain,
% 2.23/2.42      (((k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ 
% 2.23/2.42         (k7_relat_1 @ sk_B @ (k9_relat_1 @ sk_A @ sk_C)))
% 2.23/2.42         != (k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('19', plain,
% 2.23/2.42      ((((k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B)
% 2.23/2.42          != (k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C))
% 2.23/2.42        | ~ (v1_relat_1 @ sk_A)
% 2.23/2.42        | ~ (v1_relat_1 @ sk_B))),
% 2.23/2.42      inference('sup-', [status(thm)], ['17', '18'])).
% 2.23/2.42  thf('20', plain, ((v1_relat_1 @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('21', plain, ((v1_relat_1 @ sk_B)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('22', plain,
% 2.23/2.42      (((k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B)
% 2.23/2.42         != (k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 2.23/2.42      inference('demod', [status(thm)], ['19', '20', '21'])).
% 2.23/2.42  thf('23', plain,
% 2.23/2.42      ((((k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C)
% 2.23/2.42          != (k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C))
% 2.23/2.42        | ~ (v1_relat_1 @ sk_A)
% 2.23/2.42        | ~ (v1_relat_1 @ sk_B))),
% 2.23/2.42      inference('sup-', [status(thm)], ['0', '22'])).
% 2.23/2.42  thf('24', plain, ((v1_relat_1 @ sk_A)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('25', plain, ((v1_relat_1 @ sk_B)),
% 2.23/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.42  thf('26', plain,
% 2.23/2.42      (((k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C)
% 2.23/2.42         != (k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 2.23/2.42      inference('demod', [status(thm)], ['23', '24', '25'])).
% 2.23/2.42  thf('27', plain, ($false), inference('simplify', [status(thm)], ['26'])).
% 2.23/2.42  
% 2.23/2.42  % SZS output end Refutation
% 2.23/2.42  
% 2.23/2.43  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
