%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.h0u4BJrD8d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 117 expanded)
%              Number of leaves         :   25 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :  316 ( 844 expanded)
%              Number of equality atoms :   26 (  40 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_funcop_1_type,type,(
    k7_funcop_1: $i > $i > $i )).

thf(k2_funcop_1_type,type,(
    k2_funcop_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_yellow_1_type,type,(
    k6_yellow_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_yellow_1_type,type,(
    v1_yellow_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(k5_yellow_1_type,type,(
    k5_yellow_1: $i > $i > $i )).

thf(fc2_funcop_1,axiom,(
    ! [A: $i] :
      ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ A ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc2_funcop_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k2_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(redefinition_k7_funcop_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k7_funcop_1 @ A @ B )
      = ( k2_funcop_1 @ A @ B ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k7_funcop_1 @ X8 @ X9 )
      = ( k2_funcop_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_funcop_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k7_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d5_yellow_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ B )
     => ( ( k6_yellow_1 @ A @ B )
        = ( k5_yellow_1 @ A @ ( k7_funcop_1 @ A @ B ) ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k6_yellow_1 @ X4 @ X5 )
        = ( k5_yellow_1 @ X4 @ ( k7_funcop_1 @ X4 @ X5 ) ) )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_yellow_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ X0 )
        = ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t27_yellow_1,conjecture,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( k6_yellow_1 @ k1_xboole_0 @ A )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_orders_2 @ A )
       => ( ( k6_yellow_1 @ k1_xboole_0 @ A )
          = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_yellow_1])).

thf('7',plain,(
    ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
 != ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(rc1_yellow_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v1_yellow_1 @ B )
      & ( v1_partfun1 @ B @ A )
      & ( v1_funct_1 @ B )
      & ( v4_relat_1 @ B @ A )
      & ( v1_relat_1 @ B ) ) )).

thf('8',plain,(
    ! [X7: $i] :
      ( v1_partfun1 @ ( sk_B @ X7 ) @ X7 ) ),
    inference(cnf,[status(esa)],[rc1_yellow_1])).

thf(t134_pboole,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v4_relat_1 @ A @ k1_xboole_0 )
        & ( v1_funct_1 @ A )
        & ( v1_partfun1 @ A @ k1_xboole_0 ) )
     => ( A = k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ~ ( v1_partfun1 @ X10 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v4_relat_1 @ X10 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t134_pboole])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ ( sk_B @ k1_xboole_0 ) )
    | ~ ( v4_relat_1 @ ( sk_B @ k1_xboole_0 ) @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ ( sk_B @ k1_xboole_0 ) )
    | ( ( sk_B @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X7: $i] :
      ( v1_relat_1 @ ( sk_B @ X7 ) ) ),
    inference(cnf,[status(esa)],[rc1_yellow_1])).

thf('12',plain,(
    ! [X7: $i] :
      ( v4_relat_1 @ ( sk_B @ X7 ) @ X7 ) ),
    inference(cnf,[status(esa)],[rc1_yellow_1])).

thf('13',plain,(
    ! [X7: $i] :
      ( v1_funct_1 @ ( sk_B @ X7 ) ) ),
    inference(cnf,[status(esa)],[rc1_yellow_1])).

thf('14',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('15',plain,(
    ! [X7: $i] :
      ( v1_partfun1 @ ( sk_B @ X7 ) @ X7 ) ),
    inference(cnf,[status(esa)],[rc1_yellow_1])).

thf('16',plain,(
    v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t26_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v4_relat_1 @ A @ k1_xboole_0 )
        & ( v1_funct_1 @ A )
        & ( v1_partfun1 @ A @ k1_xboole_0 )
        & ( v1_yellow_1 @ A ) )
     => ( ( k5_yellow_1 @ k1_xboole_0 @ A )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) )).

thf('17',plain,(
    ! [X11: $i] :
      ( ( ( k5_yellow_1 @ k1_xboole_0 @ X11 )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) )
      | ~ ( v1_yellow_1 @ X11 )
      | ~ ( v1_partfun1 @ X11 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v4_relat_1 @ X11 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t26_yellow_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v4_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_yellow_1 @ k1_xboole_0 )
    | ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
      = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('20',plain,(
    ! [X7: $i] :
      ( v1_relat_1 @ ( sk_B @ X7 ) ) ),
    inference(cnf,[status(esa)],[rc1_yellow_1])).

thf('21',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('23',plain,(
    ! [X7: $i] :
      ( v4_relat_1 @ ( sk_B @ X7 ) @ X7 ) ),
    inference(cnf,[status(esa)],[rc1_yellow_1])).

thf('24',plain,(
    v4_relat_1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('26',plain,(
    ! [X7: $i] :
      ( v1_funct_1 @ ( sk_B @ X7 ) ) ),
    inference(cnf,[status(esa)],[rc1_yellow_1])).

thf('27',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('29',plain,(
    ! [X7: $i] :
      ( v1_yellow_1 @ ( sk_B @ X7 ) ) ),
    inference(cnf,[status(esa)],[rc1_yellow_1])).

thf('30',plain,(
    v1_yellow_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
    = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['18','21','24','27','30'])).

thf('32',plain,(
    ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
 != ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
       != ( k6_yellow_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','32'])).

thf('34',plain,(
    ~ ( l1_orders_2 @ sk_A ) ),
    inference(eq_res,[status(thm)],['33'])).

thf('35',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['34','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.h0u4BJrD8d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:43:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 79 iterations in 0.058s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.51  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.51  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.51  thf(k7_funcop_1_type, type, k7_funcop_1: $i > $i > $i).
% 0.21/0.51  thf(k2_funcop_1_type, type, k2_funcop_1: $i > $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(k6_yellow_1_type, type, k6_yellow_1: $i > $i > $i).
% 0.21/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.51  thf(v1_yellow_1_type, type, v1_yellow_1: $i > $o).
% 0.21/0.51  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.21/0.51  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.51  thf(g1_orders_2_type, type, g1_orders_2: $i > $i > $i).
% 0.21/0.51  thf(k5_yellow_1_type, type, k5_yellow_1: $i > $i > $i).
% 0.21/0.51  thf(fc2_funcop_1, axiom,
% 0.21/0.51    (![A:$i]: ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ A ) ))).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      (![X6 : $i]: (v1_xboole_0 @ (k2_funcop_1 @ k1_xboole_0 @ X6))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc2_funcop_1])).
% 0.21/0.51  thf(l13_xboole_0, axiom,
% 0.21/0.51    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.51      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X0 : $i]: ((k2_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.51  thf(redefinition_k7_funcop_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]: ( ( k7_funcop_1 @ A @ B ) = ( k2_funcop_1 @ A @ B ) ))).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X8 : $i, X9 : $i]: ((k7_funcop_1 @ X8 @ X9) = (k2_funcop_1 @ X8 @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k7_funcop_1])).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (![X0 : $i]: ((k7_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.51      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.51  thf(d5_yellow_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( l1_orders_2 @ B ) =>
% 0.21/0.51       ( ( k6_yellow_1 @ A @ B ) =
% 0.21/0.51         ( k5_yellow_1 @ A @ ( k7_funcop_1 @ A @ B ) ) ) ))).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (![X4 : $i, X5 : $i]:
% 0.21/0.51         (((k6_yellow_1 @ X4 @ X5)
% 0.21/0.51            = (k5_yellow_1 @ X4 @ (k7_funcop_1 @ X4 @ X5)))
% 0.21/0.51          | ~ (l1_orders_2 @ X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [d5_yellow_1])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((k6_yellow_1 @ k1_xboole_0 @ X0)
% 0.21/0.51            = (k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0))
% 0.21/0.51          | ~ (l1_orders_2 @ X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['4', '5'])).
% 0.21/0.51  thf(t27_yellow_1, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_orders_2 @ A ) =>
% 0.21/0.51       ( ( k6_yellow_1 @ k1_xboole_0 @ A ) =
% 0.21/0.51         ( g1_orders_2 @
% 0.21/0.51           ( k1_tarski @ k1_xboole_0 ) @ 
% 0.21/0.51           ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i]:
% 0.21/0.51        ( ( l1_orders_2 @ A ) =>
% 0.21/0.51          ( ( k6_yellow_1 @ k1_xboole_0 @ A ) =
% 0.21/0.51            ( g1_orders_2 @
% 0.21/0.51              ( k1_tarski @ k1_xboole_0 ) @ 
% 0.21/0.51              ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t27_yellow_1])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.21/0.51         != (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.21/0.51             (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(rc1_yellow_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ?[B:$i]:
% 0.21/0.51       ( ( v1_yellow_1 @ B ) & ( v1_partfun1 @ B @ A ) & ( v1_funct_1 @ B ) & 
% 0.21/0.51         ( v4_relat_1 @ B @ A ) & ( v1_relat_1 @ B ) ) ))).
% 0.21/0.51  thf('8', plain, (![X7 : $i]: (v1_partfun1 @ (sk_B @ X7) @ X7)),
% 0.21/0.51      inference('cnf', [status(esa)], [rc1_yellow_1])).
% 0.21/0.51  thf(t134_pboole, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( v1_relat_1 @ A ) & ( v4_relat_1 @ A @ k1_xboole_0 ) & 
% 0.21/0.51         ( v1_funct_1 @ A ) & ( v1_partfun1 @ A @ k1_xboole_0 ) ) =>
% 0.21/0.51       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (![X10 : $i]:
% 0.21/0.51         (((X10) = (k1_xboole_0))
% 0.21/0.51          | ~ (v1_partfun1 @ X10 @ k1_xboole_0)
% 0.21/0.51          | ~ (v1_funct_1 @ X10)
% 0.21/0.51          | ~ (v4_relat_1 @ X10 @ k1_xboole_0)
% 0.21/0.51          | ~ (v1_relat_1 @ X10))),
% 0.21/0.51      inference('cnf', [status(esa)], [t134_pboole])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      ((~ (v1_relat_1 @ (sk_B @ k1_xboole_0))
% 0.21/0.51        | ~ (v4_relat_1 @ (sk_B @ k1_xboole_0) @ k1_xboole_0)
% 0.21/0.51        | ~ (v1_funct_1 @ (sk_B @ k1_xboole_0))
% 0.21/0.51        | ((sk_B @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.51  thf('11', plain, (![X7 : $i]: (v1_relat_1 @ (sk_B @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [rc1_yellow_1])).
% 0.21/0.51  thf('12', plain, (![X7 : $i]: (v4_relat_1 @ (sk_B @ X7) @ X7)),
% 0.21/0.51      inference('cnf', [status(esa)], [rc1_yellow_1])).
% 0.21/0.51  thf('13', plain, (![X7 : $i]: (v1_funct_1 @ (sk_B @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [rc1_yellow_1])).
% 0.21/0.51  thf('14', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.51      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.21/0.51  thf('15', plain, (![X7 : $i]: (v1_partfun1 @ (sk_B @ X7) @ X7)),
% 0.21/0.51      inference('cnf', [status(esa)], [rc1_yellow_1])).
% 0.21/0.51  thf('16', plain, ((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.21/0.51      inference('sup+', [status(thm)], ['14', '15'])).
% 0.21/0.51  thf(t26_yellow_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( v1_relat_1 @ A ) & ( v4_relat_1 @ A @ k1_xboole_0 ) & 
% 0.21/0.51         ( v1_funct_1 @ A ) & ( v1_partfun1 @ A @ k1_xboole_0 ) & 
% 0.21/0.51         ( v1_yellow_1 @ A ) ) =>
% 0.21/0.51       ( ( k5_yellow_1 @ k1_xboole_0 @ A ) =
% 0.21/0.51         ( g1_orders_2 @
% 0.21/0.51           ( k1_tarski @ k1_xboole_0 ) @ 
% 0.21/0.51           ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ))).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (![X11 : $i]:
% 0.21/0.51         (((k5_yellow_1 @ k1_xboole_0 @ X11)
% 0.21/0.51            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.21/0.51               (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))
% 0.21/0.51          | ~ (v1_yellow_1 @ X11)
% 0.21/0.51          | ~ (v1_partfun1 @ X11 @ k1_xboole_0)
% 0.21/0.51          | ~ (v1_funct_1 @ X11)
% 0.21/0.51          | ~ (v4_relat_1 @ X11 @ k1_xboole_0)
% 0.21/0.51          | ~ (v1_relat_1 @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [t26_yellow_1])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      ((~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.51        | ~ (v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.21/0.51        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.21/0.51        | ~ (v1_yellow_1 @ k1_xboole_0)
% 0.21/0.51        | ((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.21/0.51            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.21/0.51               (k6_partfun1 @ (k1_tarski @ k1_xboole_0)))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.51  thf('19', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.51      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.21/0.51  thf('20', plain, (![X7 : $i]: (v1_relat_1 @ (sk_B @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [rc1_yellow_1])).
% 0.21/0.51  thf('21', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.51      inference('sup+', [status(thm)], ['19', '20'])).
% 0.21/0.51  thf('22', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.51      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.21/0.51  thf('23', plain, (![X7 : $i]: (v4_relat_1 @ (sk_B @ X7) @ X7)),
% 0.21/0.51      inference('cnf', [status(esa)], [rc1_yellow_1])).
% 0.21/0.51  thf('24', plain, ((v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.21/0.51      inference('sup+', [status(thm)], ['22', '23'])).
% 0.21/0.51  thf('25', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.51      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.21/0.51  thf('26', plain, (![X7 : $i]: (v1_funct_1 @ (sk_B @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [rc1_yellow_1])).
% 0.21/0.51  thf('27', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.21/0.51      inference('sup+', [status(thm)], ['25', '26'])).
% 0.21/0.51  thf('28', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.51      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.21/0.51  thf('29', plain, (![X7 : $i]: (v1_yellow_1 @ (sk_B @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [rc1_yellow_1])).
% 0.21/0.51  thf('30', plain, ((v1_yellow_1 @ k1_xboole_0)),
% 0.21/0.51      inference('sup+', [status(thm)], ['28', '29'])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      (((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.21/0.51         = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.21/0.51            (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))),
% 0.21/0.51      inference('demod', [status(thm)], ['18', '21', '24', '27', '30'])).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.21/0.51         != (k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0))),
% 0.21/0.51      inference('demod', [status(thm)], ['7', '31'])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.21/0.51            != (k6_yellow_1 @ k1_xboole_0 @ X0))
% 0.21/0.51          | ~ (l1_orders_2 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['6', '32'])).
% 0.21/0.51  thf('34', plain, (~ (l1_orders_2 @ sk_A)),
% 0.21/0.51      inference('eq_res', [status(thm)], ['33'])).
% 0.21/0.51  thf('35', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('36', plain, ($false), inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
