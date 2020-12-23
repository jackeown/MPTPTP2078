%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.44kR0gLGqF

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:54 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :   63 (  89 expanded)
%              Number of leaves         :   16 (  33 expanded)
%              Depth                    :   12
%              Number of atoms          :  386 ( 675 expanded)
%              Number of equality atoms :   15 (  20 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t31_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( r1_tarski @ A @ B )
             => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X23: $i] :
      ( ( ( k3_relat_1 @ X23 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X23 ) @ ( k2_relat_1 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('2',plain,(
    ! [X23: $i] :
      ( ( ( k3_relat_1 @ X23 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X23 ) @ ( k2_relat_1 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ( r1_tarski @ ( k1_relat_1 @ X25 ) @ ( k1_relat_1 @ X24 ) )
      | ~ ( r1_tarski @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('12',plain,
    ( ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t9_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_tarski @ ( k2_xboole_0 @ X15 @ X17 ) @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t9_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k2_xboole_0 @ ( k3_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k2_xboole_0 @ ( k3_relat_1 @ sk_B ) @ ( k2_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','19'])).

thf('21',plain,(
    ! [X23: $i] :
      ( ( ( k3_relat_1 @ X23 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X23 ) @ ( k2_relat_1 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('23',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('26',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ( r1_tarski @ ( k2_relat_1 @ X25 ) @ ( k2_relat_1 @ X24 ) )
      | ~ ( r1_tarski @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('33',plain,
    ( ( k2_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('40',plain,
    ( ( k2_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    = ( k3_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('42',plain,
    ( ( k2_xboole_0 @ ( k3_relat_1 @ sk_B ) @ ( k2_relat_1 @ sk_A ) )
    = ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['20','42','43'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['0','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.44kR0gLGqF
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 15:16:41 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 1.06/1.27  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.06/1.27  % Solved by: fo/fo7.sh
% 1.06/1.27  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.06/1.27  % done 1399 iterations in 0.804s
% 1.06/1.27  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.06/1.27  % SZS output start Refutation
% 1.06/1.27  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.06/1.27  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 1.06/1.27  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.06/1.27  thf(sk_A_type, type, sk_A: $i).
% 1.06/1.27  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.06/1.27  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.06/1.27  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.06/1.27  thf(sk_B_type, type, sk_B: $i).
% 1.06/1.27  thf(t31_relat_1, conjecture,
% 1.06/1.27    (![A:$i]:
% 1.06/1.27     ( ( v1_relat_1 @ A ) =>
% 1.06/1.27       ( ![B:$i]:
% 1.06/1.27         ( ( v1_relat_1 @ B ) =>
% 1.06/1.27           ( ( r1_tarski @ A @ B ) =>
% 1.06/1.27             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 1.06/1.27  thf(zf_stmt_0, negated_conjecture,
% 1.06/1.27    (~( ![A:$i]:
% 1.06/1.27        ( ( v1_relat_1 @ A ) =>
% 1.06/1.27          ( ![B:$i]:
% 1.06/1.27            ( ( v1_relat_1 @ B ) =>
% 1.06/1.27              ( ( r1_tarski @ A @ B ) =>
% 1.06/1.27                ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 1.06/1.27    inference('cnf.neg', [status(esa)], [t31_relat_1])).
% 1.06/1.27  thf('0', plain, (~ (r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf(d6_relat_1, axiom,
% 1.06/1.27    (![A:$i]:
% 1.06/1.27     ( ( v1_relat_1 @ A ) =>
% 1.06/1.27       ( ( k3_relat_1 @ A ) =
% 1.06/1.27         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 1.06/1.27  thf('1', plain,
% 1.06/1.27      (![X23 : $i]:
% 1.06/1.27         (((k3_relat_1 @ X23)
% 1.06/1.27            = (k2_xboole_0 @ (k1_relat_1 @ X23) @ (k2_relat_1 @ X23)))
% 1.06/1.27          | ~ (v1_relat_1 @ X23))),
% 1.06/1.27      inference('cnf', [status(esa)], [d6_relat_1])).
% 1.06/1.27  thf('2', plain,
% 1.06/1.27      (![X23 : $i]:
% 1.06/1.27         (((k3_relat_1 @ X23)
% 1.06/1.27            = (k2_xboole_0 @ (k1_relat_1 @ X23) @ (k2_relat_1 @ X23)))
% 1.06/1.27          | ~ (v1_relat_1 @ X23))),
% 1.06/1.27      inference('cnf', [status(esa)], [d6_relat_1])).
% 1.06/1.27  thf(t7_xboole_1, axiom,
% 1.06/1.27    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.06/1.27  thf('3', plain,
% 1.06/1.27      (![X13 : $i, X14 : $i]: (r1_tarski @ X13 @ (k2_xboole_0 @ X13 @ X14))),
% 1.06/1.27      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.06/1.27  thf('4', plain,
% 1.06/1.27      (![X0 : $i]:
% 1.06/1.27         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 1.06/1.27          | ~ (v1_relat_1 @ X0))),
% 1.06/1.27      inference('sup+', [status(thm)], ['2', '3'])).
% 1.06/1.27  thf('5', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf(t25_relat_1, axiom,
% 1.06/1.27    (![A:$i]:
% 1.06/1.27     ( ( v1_relat_1 @ A ) =>
% 1.06/1.27       ( ![B:$i]:
% 1.06/1.27         ( ( v1_relat_1 @ B ) =>
% 1.06/1.27           ( ( r1_tarski @ A @ B ) =>
% 1.06/1.27             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 1.06/1.27               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 1.06/1.27  thf('6', plain,
% 1.06/1.27      (![X24 : $i, X25 : $i]:
% 1.06/1.27         (~ (v1_relat_1 @ X24)
% 1.06/1.27          | (r1_tarski @ (k1_relat_1 @ X25) @ (k1_relat_1 @ X24))
% 1.06/1.27          | ~ (r1_tarski @ X25 @ X24)
% 1.06/1.27          | ~ (v1_relat_1 @ X25))),
% 1.06/1.27      inference('cnf', [status(esa)], [t25_relat_1])).
% 1.06/1.27  thf('7', plain,
% 1.06/1.27      ((~ (v1_relat_1 @ sk_A)
% 1.06/1.27        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 1.06/1.27        | ~ (v1_relat_1 @ sk_B))),
% 1.06/1.27      inference('sup-', [status(thm)], ['5', '6'])).
% 1.06/1.27  thf('8', plain, ((v1_relat_1 @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('9', plain, ((v1_relat_1 @ sk_B)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('10', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))),
% 1.06/1.27      inference('demod', [status(thm)], ['7', '8', '9'])).
% 1.06/1.27  thf(t12_xboole_1, axiom,
% 1.06/1.27    (![A:$i,B:$i]:
% 1.06/1.27     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.06/1.27  thf('11', plain,
% 1.06/1.27      (![X11 : $i, X12 : $i]:
% 1.06/1.27         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 1.06/1.27      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.06/1.27  thf('12', plain,
% 1.06/1.27      (((k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 1.06/1.27         = (k1_relat_1 @ sk_B))),
% 1.06/1.27      inference('sup-', [status(thm)], ['10', '11'])).
% 1.06/1.27  thf(t11_xboole_1, axiom,
% 1.06/1.27    (![A:$i,B:$i,C:$i]:
% 1.06/1.27     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 1.06/1.27  thf('13', plain,
% 1.06/1.27      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.06/1.27         ((r1_tarski @ X8 @ X9) | ~ (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 1.06/1.27      inference('cnf', [status(esa)], [t11_xboole_1])).
% 1.06/1.27  thf('14', plain,
% 1.06/1.27      (![X0 : $i]:
% 1.06/1.27         (~ (r1_tarski @ (k1_relat_1 @ sk_B) @ X0)
% 1.06/1.27          | (r1_tarski @ (k1_relat_1 @ sk_A) @ X0))),
% 1.06/1.27      inference('sup-', [status(thm)], ['12', '13'])).
% 1.06/1.27  thf('15', plain,
% 1.06/1.27      ((~ (v1_relat_1 @ sk_B)
% 1.06/1.27        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 1.06/1.27      inference('sup-', [status(thm)], ['4', '14'])).
% 1.06/1.27  thf('16', plain, ((v1_relat_1 @ sk_B)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('17', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 1.06/1.27      inference('demod', [status(thm)], ['15', '16'])).
% 1.06/1.27  thf(t9_xboole_1, axiom,
% 1.06/1.27    (![A:$i,B:$i,C:$i]:
% 1.06/1.27     ( ( r1_tarski @ A @ B ) =>
% 1.06/1.27       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.06/1.27  thf('18', plain,
% 1.06/1.27      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.06/1.27         (~ (r1_tarski @ X15 @ X16)
% 1.06/1.27          | (r1_tarski @ (k2_xboole_0 @ X15 @ X17) @ (k2_xboole_0 @ X16 @ X17)))),
% 1.06/1.27      inference('cnf', [status(esa)], [t9_xboole_1])).
% 1.06/1.27  thf('19', plain,
% 1.06/1.27      (![X0 : $i]:
% 1.06/1.27         (r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 1.06/1.27          (k2_xboole_0 @ (k3_relat_1 @ sk_B) @ X0))),
% 1.06/1.27      inference('sup-', [status(thm)], ['17', '18'])).
% 1.06/1.27  thf('20', plain,
% 1.06/1.27      (((r1_tarski @ (k3_relat_1 @ sk_A) @ 
% 1.06/1.27         (k2_xboole_0 @ (k3_relat_1 @ sk_B) @ (k2_relat_1 @ sk_A)))
% 1.06/1.27        | ~ (v1_relat_1 @ sk_A))),
% 1.06/1.27      inference('sup+', [status(thm)], ['1', '19'])).
% 1.06/1.27  thf('21', plain,
% 1.06/1.27      (![X23 : $i]:
% 1.06/1.27         (((k3_relat_1 @ X23)
% 1.06/1.27            = (k2_xboole_0 @ (k1_relat_1 @ X23) @ (k2_relat_1 @ X23)))
% 1.06/1.27          | ~ (v1_relat_1 @ X23))),
% 1.06/1.27      inference('cnf', [status(esa)], [d6_relat_1])).
% 1.06/1.27  thf(commutativity_k2_xboole_0, axiom,
% 1.06/1.27    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.06/1.27  thf('22', plain,
% 1.06/1.27      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.06/1.27      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.06/1.27  thf('23', plain,
% 1.06/1.27      (![X13 : $i, X14 : $i]: (r1_tarski @ X13 @ (k2_xboole_0 @ X13 @ X14))),
% 1.06/1.27      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.06/1.27  thf('24', plain,
% 1.06/1.27      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.06/1.27      inference('sup+', [status(thm)], ['22', '23'])).
% 1.06/1.27  thf('25', plain,
% 1.06/1.27      (![X0 : $i]:
% 1.06/1.27         ((r1_tarski @ (k2_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 1.06/1.27          | ~ (v1_relat_1 @ X0))),
% 1.06/1.27      inference('sup+', [status(thm)], ['21', '24'])).
% 1.06/1.27  thf('26', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('27', plain,
% 1.06/1.27      (![X24 : $i, X25 : $i]:
% 1.06/1.27         (~ (v1_relat_1 @ X24)
% 1.06/1.27          | (r1_tarski @ (k2_relat_1 @ X25) @ (k2_relat_1 @ X24))
% 1.06/1.27          | ~ (r1_tarski @ X25 @ X24)
% 1.06/1.27          | ~ (v1_relat_1 @ X25))),
% 1.06/1.27      inference('cnf', [status(esa)], [t25_relat_1])).
% 1.06/1.27  thf('28', plain,
% 1.06/1.27      ((~ (v1_relat_1 @ sk_A)
% 1.06/1.27        | (r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))
% 1.06/1.27        | ~ (v1_relat_1 @ sk_B))),
% 1.06/1.27      inference('sup-', [status(thm)], ['26', '27'])).
% 1.06/1.27  thf('29', plain, ((v1_relat_1 @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('31', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))),
% 1.06/1.27      inference('demod', [status(thm)], ['28', '29', '30'])).
% 1.06/1.27  thf('32', plain,
% 1.06/1.27      (![X11 : $i, X12 : $i]:
% 1.06/1.27         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 1.06/1.27      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.06/1.27  thf('33', plain,
% 1.06/1.27      (((k2_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))
% 1.06/1.27         = (k2_relat_1 @ sk_B))),
% 1.06/1.27      inference('sup-', [status(thm)], ['31', '32'])).
% 1.06/1.27  thf('34', plain,
% 1.06/1.27      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.06/1.27         ((r1_tarski @ X8 @ X9) | ~ (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 1.06/1.27      inference('cnf', [status(esa)], [t11_xboole_1])).
% 1.06/1.27  thf('35', plain,
% 1.06/1.27      (![X0 : $i]:
% 1.06/1.27         (~ (r1_tarski @ (k2_relat_1 @ sk_B) @ X0)
% 1.06/1.27          | (r1_tarski @ (k2_relat_1 @ sk_A) @ X0))),
% 1.06/1.27      inference('sup-', [status(thm)], ['33', '34'])).
% 1.06/1.27  thf('36', plain,
% 1.06/1.27      ((~ (v1_relat_1 @ sk_B)
% 1.06/1.27        | (r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 1.06/1.27      inference('sup-', [status(thm)], ['25', '35'])).
% 1.06/1.27  thf('37', plain, ((v1_relat_1 @ sk_B)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('38', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 1.06/1.27      inference('demod', [status(thm)], ['36', '37'])).
% 1.06/1.27  thf('39', plain,
% 1.06/1.27      (![X11 : $i, X12 : $i]:
% 1.06/1.27         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 1.06/1.27      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.06/1.27  thf('40', plain,
% 1.06/1.27      (((k2_xboole_0 @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))
% 1.06/1.27         = (k3_relat_1 @ sk_B))),
% 1.06/1.27      inference('sup-', [status(thm)], ['38', '39'])).
% 1.06/1.27  thf('41', plain,
% 1.06/1.27      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.06/1.27      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.06/1.27  thf('42', plain,
% 1.06/1.27      (((k2_xboole_0 @ (k3_relat_1 @ sk_B) @ (k2_relat_1 @ sk_A))
% 1.06/1.27         = (k3_relat_1 @ sk_B))),
% 1.06/1.27      inference('demod', [status(thm)], ['40', '41'])).
% 1.06/1.27  thf('43', plain, ((v1_relat_1 @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('44', plain, ((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 1.06/1.27      inference('demod', [status(thm)], ['20', '42', '43'])).
% 1.06/1.27  thf('45', plain, ($false), inference('demod', [status(thm)], ['0', '44'])).
% 1.06/1.27  
% 1.06/1.27  % SZS output end Refutation
% 1.06/1.27  
% 1.06/1.28  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
