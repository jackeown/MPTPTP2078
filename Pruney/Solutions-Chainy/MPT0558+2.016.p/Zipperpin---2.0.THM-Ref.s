%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TCZPrRGIae

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:36 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   53 (  59 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :   14
%              Number of atoms          :  488 ( 553 expanded)
%              Number of equality atoms :   31 (  36 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X3 @ X4 ) )
        = ( k9_relat_1 @ X3 @ X4 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k7_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X15 ) @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('2',plain,(
    ! [X14: $i] :
      ( ( ( k5_relat_1 @ X14 @ ( k6_relat_1 @ ( k2_relat_1 @ X14 ) ) )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) @ X11 )
        = ( k5_relat_1 @ X10 @ ( k5_relat_1 @ X9 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

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
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) ) @ ( k1_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
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
    ! [X12: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
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

thf(t47_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X7 @ X8 ) )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X8 ) @ ( k2_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
        = ( k2_relat_1 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
        = ( k2_relat_1 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
        = ( k2_relat_1 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k2_relat_1 @ ( k7_relat_1 @ X0 @ ( k2_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k2_relat_1 @ ( k7_relat_1 @ X0 @ ( k2_relat_1 @ X1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) )
        = ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) )
        = ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf(t160_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t160_relat_1])).

thf('26',plain,(
    ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
 != ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_A ) )
     != ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_A ) )
 != ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    $false ),
    inference(simplify,[status(thm)],['30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TCZPrRGIae
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:37:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.59/0.85  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.85  % Solved by: fo/fo7.sh
% 0.59/0.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.85  % done 421 iterations in 0.393s
% 0.59/0.85  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.85  % SZS output start Refutation
% 0.59/0.85  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.59/0.85  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.85  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.59/0.85  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.85  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.59/0.85  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.59/0.85  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.85  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.59/0.85  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.59/0.85  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.59/0.85  thf(t148_relat_1, axiom,
% 0.59/0.85    (![A:$i,B:$i]:
% 0.59/0.85     ( ( v1_relat_1 @ B ) =>
% 0.59/0.85       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.59/0.85  thf('0', plain,
% 0.59/0.85      (![X3 : $i, X4 : $i]:
% 0.59/0.85         (((k2_relat_1 @ (k7_relat_1 @ X3 @ X4)) = (k9_relat_1 @ X3 @ X4))
% 0.59/0.85          | ~ (v1_relat_1 @ X3))),
% 0.59/0.85      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.59/0.85  thf(t94_relat_1, axiom,
% 0.59/0.85    (![A:$i,B:$i]:
% 0.59/0.85     ( ( v1_relat_1 @ B ) =>
% 0.59/0.85       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.59/0.85  thf('1', plain,
% 0.59/0.85      (![X15 : $i, X16 : $i]:
% 0.59/0.85         (((k7_relat_1 @ X16 @ X15) = (k5_relat_1 @ (k6_relat_1 @ X15) @ X16))
% 0.59/0.85          | ~ (v1_relat_1 @ X16))),
% 0.59/0.85      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.59/0.85  thf(t80_relat_1, axiom,
% 0.59/0.85    (![A:$i]:
% 0.59/0.85     ( ( v1_relat_1 @ A ) =>
% 0.59/0.85       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.59/0.85  thf('2', plain,
% 0.59/0.85      (![X14 : $i]:
% 0.59/0.85         (((k5_relat_1 @ X14 @ (k6_relat_1 @ (k2_relat_1 @ X14))) = (X14))
% 0.59/0.85          | ~ (v1_relat_1 @ X14))),
% 0.59/0.85      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.59/0.85  thf(t55_relat_1, axiom,
% 0.59/0.85    (![A:$i]:
% 0.59/0.85     ( ( v1_relat_1 @ A ) =>
% 0.59/0.85       ( ![B:$i]:
% 0.59/0.85         ( ( v1_relat_1 @ B ) =>
% 0.59/0.85           ( ![C:$i]:
% 0.59/0.85             ( ( v1_relat_1 @ C ) =>
% 0.59/0.85               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.59/0.85                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.59/0.85  thf('3', plain,
% 0.59/0.85      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.59/0.85         (~ (v1_relat_1 @ X9)
% 0.59/0.85          | ((k5_relat_1 @ (k5_relat_1 @ X10 @ X9) @ X11)
% 0.59/0.85              = (k5_relat_1 @ X10 @ (k5_relat_1 @ X9 @ X11)))
% 0.59/0.85          | ~ (v1_relat_1 @ X11)
% 0.59/0.85          | ~ (v1_relat_1 @ X10))),
% 0.59/0.85      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.59/0.85  thf('4', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         (((k5_relat_1 @ X0 @ X1)
% 0.59/0.85            = (k5_relat_1 @ X0 @ 
% 0.59/0.85               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1)))
% 0.59/0.85          | ~ (v1_relat_1 @ X0)
% 0.59/0.85          | ~ (v1_relat_1 @ X0)
% 0.59/0.85          | ~ (v1_relat_1 @ X1)
% 0.59/0.85          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))),
% 0.59/0.85      inference('sup+', [status(thm)], ['2', '3'])).
% 0.59/0.85  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.59/0.85  thf('5', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 0.59/0.85      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.59/0.85  thf('6', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         (((k5_relat_1 @ X0 @ X1)
% 0.59/0.85            = (k5_relat_1 @ X0 @ 
% 0.59/0.85               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1)))
% 0.59/0.85          | ~ (v1_relat_1 @ X0)
% 0.59/0.85          | ~ (v1_relat_1 @ X0)
% 0.59/0.85          | ~ (v1_relat_1 @ X1))),
% 0.59/0.85      inference('demod', [status(thm)], ['4', '5'])).
% 0.59/0.85  thf('7', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         (~ (v1_relat_1 @ X1)
% 0.59/0.85          | ~ (v1_relat_1 @ X0)
% 0.59/0.85          | ((k5_relat_1 @ X0 @ X1)
% 0.59/0.85              = (k5_relat_1 @ X0 @ 
% 0.59/0.85                 (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1))))),
% 0.59/0.85      inference('simplify', [status(thm)], ['6'])).
% 0.59/0.85  thf('8', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         (((k5_relat_1 @ X0 @ X1)
% 0.59/0.85            = (k5_relat_1 @ X0 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0))))
% 0.59/0.85          | ~ (v1_relat_1 @ X1)
% 0.59/0.85          | ~ (v1_relat_1 @ X0)
% 0.59/0.85          | ~ (v1_relat_1 @ X1))),
% 0.59/0.85      inference('sup+', [status(thm)], ['1', '7'])).
% 0.59/0.85  thf('9', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         (~ (v1_relat_1 @ X0)
% 0.59/0.85          | ~ (v1_relat_1 @ X1)
% 0.59/0.85          | ((k5_relat_1 @ X0 @ X1)
% 0.59/0.85              = (k5_relat_1 @ X0 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0)))))),
% 0.59/0.85      inference('simplify', [status(thm)], ['8'])).
% 0.59/0.85  thf(dt_k7_relat_1, axiom,
% 0.59/0.85    (![A:$i,B:$i]:
% 0.59/0.85     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.59/0.85  thf('10', plain,
% 0.59/0.85      (![X1 : $i, X2 : $i]:
% 0.59/0.85         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X2)))),
% 0.59/0.85      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.59/0.85  thf('11', plain,
% 0.59/0.85      (![X15 : $i, X16 : $i]:
% 0.59/0.85         (((k7_relat_1 @ X16 @ X15) = (k5_relat_1 @ (k6_relat_1 @ X15) @ X16))
% 0.59/0.85          | ~ (v1_relat_1 @ X16))),
% 0.59/0.85      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.59/0.85  thf(t44_relat_1, axiom,
% 0.59/0.85    (![A:$i]:
% 0.59/0.85     ( ( v1_relat_1 @ A ) =>
% 0.59/0.85       ( ![B:$i]:
% 0.59/0.85         ( ( v1_relat_1 @ B ) =>
% 0.59/0.85           ( r1_tarski @
% 0.59/0.85             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.59/0.85  thf('12', plain,
% 0.59/0.85      (![X5 : $i, X6 : $i]:
% 0.59/0.85         (~ (v1_relat_1 @ X5)
% 0.59/0.85          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X6 @ X5)) @ 
% 0.59/0.85             (k1_relat_1 @ X6))
% 0.59/0.85          | ~ (v1_relat_1 @ X6))),
% 0.59/0.85      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.59/0.85  thf('13', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 0.59/0.85           (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.59/0.85          | ~ (v1_relat_1 @ X1)
% 0.59/0.85          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.59/0.85          | ~ (v1_relat_1 @ X1))),
% 0.59/0.85      inference('sup+', [status(thm)], ['11', '12'])).
% 0.59/0.85  thf(t71_relat_1, axiom,
% 0.59/0.85    (![A:$i]:
% 0.59/0.85     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.59/0.85       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.59/0.85  thf('14', plain, (![X12 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 0.59/0.85      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.59/0.85  thf('15', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 0.59/0.85      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.59/0.85  thf('16', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0)
% 0.59/0.85          | ~ (v1_relat_1 @ X1)
% 0.59/0.85          | ~ (v1_relat_1 @ X1))),
% 0.59/0.85      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.59/0.85  thf('17', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         (~ (v1_relat_1 @ X1)
% 0.59/0.85          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0))),
% 0.59/0.85      inference('simplify', [status(thm)], ['16'])).
% 0.59/0.85  thf(t47_relat_1, axiom,
% 0.59/0.85    (![A:$i]:
% 0.59/0.85     ( ( v1_relat_1 @ A ) =>
% 0.59/0.85       ( ![B:$i]:
% 0.59/0.85         ( ( v1_relat_1 @ B ) =>
% 0.59/0.85           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.59/0.85             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.59/0.85  thf('18', plain,
% 0.59/0.85      (![X7 : $i, X8 : $i]:
% 0.59/0.85         (~ (v1_relat_1 @ X7)
% 0.59/0.85          | ((k2_relat_1 @ (k5_relat_1 @ X7 @ X8)) = (k2_relat_1 @ X8))
% 0.59/0.85          | ~ (r1_tarski @ (k1_relat_1 @ X8) @ (k2_relat_1 @ X7))
% 0.59/0.85          | ~ (v1_relat_1 @ X8))),
% 0.59/0.85      inference('cnf', [status(esa)], [t47_relat_1])).
% 0.59/0.85  thf('19', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         (~ (v1_relat_1 @ X1)
% 0.59/0.85          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0)))
% 0.59/0.85          | ((k2_relat_1 @ 
% 0.59/0.85              (k5_relat_1 @ X0 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0))))
% 0.59/0.85              = (k2_relat_1 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0))))
% 0.59/0.85          | ~ (v1_relat_1 @ X0))),
% 0.59/0.85      inference('sup-', [status(thm)], ['17', '18'])).
% 0.59/0.85  thf('20', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         (~ (v1_relat_1 @ X1)
% 0.59/0.85          | ~ (v1_relat_1 @ X0)
% 0.59/0.85          | ((k2_relat_1 @ 
% 0.59/0.85              (k5_relat_1 @ X0 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0))))
% 0.59/0.85              = (k2_relat_1 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0))))
% 0.59/0.85          | ~ (v1_relat_1 @ X1))),
% 0.59/0.85      inference('sup-', [status(thm)], ['10', '19'])).
% 0.59/0.85  thf('21', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         (((k2_relat_1 @ 
% 0.59/0.85            (k5_relat_1 @ X0 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0))))
% 0.59/0.85            = (k2_relat_1 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0))))
% 0.59/0.85          | ~ (v1_relat_1 @ X0)
% 0.59/0.85          | ~ (v1_relat_1 @ X1))),
% 0.59/0.85      inference('simplify', [status(thm)], ['20'])).
% 0.59/0.85  thf('22', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         (((k2_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.59/0.85            = (k2_relat_1 @ (k7_relat_1 @ X0 @ (k2_relat_1 @ X1))))
% 0.59/0.85          | ~ (v1_relat_1 @ X0)
% 0.59/0.85          | ~ (v1_relat_1 @ X1)
% 0.59/0.85          | ~ (v1_relat_1 @ X0)
% 0.59/0.85          | ~ (v1_relat_1 @ X1))),
% 0.59/0.85      inference('sup+', [status(thm)], ['9', '21'])).
% 0.59/0.85  thf('23', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         (~ (v1_relat_1 @ X1)
% 0.59/0.85          | ~ (v1_relat_1 @ X0)
% 0.59/0.85          | ((k2_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.59/0.85              = (k2_relat_1 @ (k7_relat_1 @ X0 @ (k2_relat_1 @ X1)))))),
% 0.59/0.85      inference('simplify', [status(thm)], ['22'])).
% 0.59/0.85  thf('24', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         (((k2_relat_1 @ (k5_relat_1 @ X0 @ X1))
% 0.59/0.85            = (k9_relat_1 @ X1 @ (k2_relat_1 @ X0)))
% 0.59/0.85          | ~ (v1_relat_1 @ X1)
% 0.59/0.85          | ~ (v1_relat_1 @ X1)
% 0.59/0.85          | ~ (v1_relat_1 @ X0))),
% 0.59/0.85      inference('sup+', [status(thm)], ['0', '23'])).
% 0.59/0.85  thf('25', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         (~ (v1_relat_1 @ X0)
% 0.59/0.85          | ~ (v1_relat_1 @ X1)
% 0.59/0.85          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ X1))
% 0.59/0.85              = (k9_relat_1 @ X1 @ (k2_relat_1 @ X0))))),
% 0.59/0.85      inference('simplify', [status(thm)], ['24'])).
% 0.59/0.85  thf(t160_relat_1, conjecture,
% 0.59/0.85    (![A:$i]:
% 0.59/0.85     ( ( v1_relat_1 @ A ) =>
% 0.59/0.85       ( ![B:$i]:
% 0.59/0.85         ( ( v1_relat_1 @ B ) =>
% 0.59/0.85           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.59/0.85             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.59/0.85  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.85    (~( ![A:$i]:
% 0.59/0.85        ( ( v1_relat_1 @ A ) =>
% 0.59/0.85          ( ![B:$i]:
% 0.59/0.85            ( ( v1_relat_1 @ B ) =>
% 0.59/0.85              ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.59/0.85                ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 0.59/0.85    inference('cnf.neg', [status(esa)], [t160_relat_1])).
% 0.59/0.85  thf('26', plain,
% 0.59/0.85      (((k2_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))
% 0.59/0.85         != (k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_A)))),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.85  thf('27', plain,
% 0.59/0.85      ((((k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_A))
% 0.59/0.85          != (k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_A)))
% 0.59/0.85        | ~ (v1_relat_1 @ sk_B)
% 0.59/0.85        | ~ (v1_relat_1 @ sk_A))),
% 0.59/0.85      inference('sup-', [status(thm)], ['25', '26'])).
% 0.59/0.85  thf('28', plain, ((v1_relat_1 @ sk_B)),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.85  thf('29', plain, ((v1_relat_1 @ sk_A)),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.85  thf('30', plain,
% 0.59/0.85      (((k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_A))
% 0.59/0.85         != (k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_A)))),
% 0.59/0.85      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.59/0.85  thf('31', plain, ($false), inference('simplify', [status(thm)], ['30'])).
% 0.59/0.85  
% 0.59/0.85  % SZS output end Refutation
% 0.59/0.85  
% 0.72/0.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
