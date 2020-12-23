%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.y8K69JIpRz

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:59 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 105 expanded)
%              Number of leaves         :   15 (  37 expanded)
%              Depth                    :   16
%              Number of atoms          :  369 ( 845 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

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
    ! [X11: $i] :
      ( ( ( k3_relat_1 @ X11 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X11 ) @ ( k2_relat_1 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('2',plain,(
    ! [X11: $i] :
      ( ( ( k3_relat_1 @ X11 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X11 ) @ ( k2_relat_1 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('3',plain,(
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

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( r1_tarski @ ( k2_relat_1 @ X13 ) @ ( k2_relat_1 @ X12 ) )
      | ~ ( r1_tarski @ X13 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('5',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('15',plain,(
    ! [X11: $i] :
      ( ( ( k3_relat_1 @ X11 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X11 ) @ ( k2_relat_1 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('18',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k2_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k2_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('24',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k3_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( r1_tarski @ ( k1_relat_1 @ X13 ) @ ( k1_relat_1 @ X12 ) )
      | ~ ( r1_tarski @ X13 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['26','34'])).

thf('36',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k3_relat_1 @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( k3_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','37'])).

thf('39',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['0','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.14/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.y8K69JIpRz
% 0.16/0.35  % Computer   : n010.cluster.edu
% 0.16/0.35  % Model      : x86_64 x86_64
% 0.16/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.35  % Memory     : 8042.1875MB
% 0.16/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.35  % CPULimit   : 60
% 0.16/0.35  % DateTime   : Tue Dec  1 16:10:29 EST 2020
% 0.16/0.35  % CPUTime    : 
% 0.16/0.35  % Running portfolio for 600 s
% 0.16/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.35  % Number of cores: 8
% 0.16/0.35  % Python version: Python 3.6.8
% 0.22/0.36  % Running in FO mode
% 0.55/0.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.55/0.72  % Solved by: fo/fo7.sh
% 0.55/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.72  % done 342 iterations in 0.257s
% 0.55/0.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.55/0.72  % SZS output start Refutation
% 0.55/0.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.55/0.72  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.55/0.72  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.55/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.55/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.72  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.55/0.72  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.55/0.72  thf(t31_relat_1, conjecture,
% 0.55/0.72    (![A:$i]:
% 0.55/0.72     ( ( v1_relat_1 @ A ) =>
% 0.55/0.72       ( ![B:$i]:
% 0.55/0.72         ( ( v1_relat_1 @ B ) =>
% 0.55/0.72           ( ( r1_tarski @ A @ B ) =>
% 0.55/0.72             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 0.55/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.72    (~( ![A:$i]:
% 0.55/0.72        ( ( v1_relat_1 @ A ) =>
% 0.55/0.72          ( ![B:$i]:
% 0.55/0.72            ( ( v1_relat_1 @ B ) =>
% 0.55/0.72              ( ( r1_tarski @ A @ B ) =>
% 0.55/0.72                ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 0.55/0.72    inference('cnf.neg', [status(esa)], [t31_relat_1])).
% 0.55/0.72  thf('0', plain, (~ (r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf(d6_relat_1, axiom,
% 0.55/0.72    (![A:$i]:
% 0.55/0.72     ( ( v1_relat_1 @ A ) =>
% 0.55/0.72       ( ( k3_relat_1 @ A ) =
% 0.55/0.72         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.55/0.72  thf('1', plain,
% 0.55/0.72      (![X11 : $i]:
% 0.55/0.72         (((k3_relat_1 @ X11)
% 0.55/0.72            = (k2_xboole_0 @ (k1_relat_1 @ X11) @ (k2_relat_1 @ X11)))
% 0.55/0.72          | ~ (v1_relat_1 @ X11))),
% 0.55/0.72      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.55/0.72  thf('2', plain,
% 0.55/0.72      (![X11 : $i]:
% 0.55/0.72         (((k3_relat_1 @ X11)
% 0.55/0.72            = (k2_xboole_0 @ (k1_relat_1 @ X11) @ (k2_relat_1 @ X11)))
% 0.55/0.72          | ~ (v1_relat_1 @ X11))),
% 0.55/0.72      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.55/0.72  thf('3', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf(t25_relat_1, axiom,
% 0.55/0.72    (![A:$i]:
% 0.55/0.72     ( ( v1_relat_1 @ A ) =>
% 0.55/0.72       ( ![B:$i]:
% 0.55/0.72         ( ( v1_relat_1 @ B ) =>
% 0.55/0.72           ( ( r1_tarski @ A @ B ) =>
% 0.55/0.72             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.55/0.72               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.55/0.72  thf('4', plain,
% 0.55/0.72      (![X12 : $i, X13 : $i]:
% 0.55/0.72         (~ (v1_relat_1 @ X12)
% 0.55/0.72          | (r1_tarski @ (k2_relat_1 @ X13) @ (k2_relat_1 @ X12))
% 0.55/0.72          | ~ (r1_tarski @ X13 @ X12)
% 0.55/0.72          | ~ (v1_relat_1 @ X13))),
% 0.55/0.72      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.55/0.72  thf('5', plain,
% 0.55/0.72      ((~ (v1_relat_1 @ sk_A)
% 0.55/0.72        | (r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))
% 0.55/0.72        | ~ (v1_relat_1 @ sk_B))),
% 0.55/0.72      inference('sup-', [status(thm)], ['3', '4'])).
% 0.55/0.72  thf('6', plain, ((v1_relat_1 @ sk_A)),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('7', plain, ((v1_relat_1 @ sk_B)),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('8', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))),
% 0.55/0.72      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.55/0.72  thf(t10_xboole_1, axiom,
% 0.55/0.72    (![A:$i,B:$i,C:$i]:
% 0.55/0.72     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.55/0.72  thf('9', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.72         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ X1)))),
% 0.55/0.72      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.55/0.72  thf('10', plain,
% 0.55/0.72      (![X0 : $i]:
% 0.55/0.72         (r1_tarski @ (k2_relat_1 @ sk_A) @ 
% 0.55/0.72          (k2_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)))),
% 0.55/0.72      inference('sup-', [status(thm)], ['8', '9'])).
% 0.55/0.72  thf('11', plain,
% 0.55/0.72      (((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))
% 0.55/0.72        | ~ (v1_relat_1 @ sk_B))),
% 0.55/0.72      inference('sup+', [status(thm)], ['2', '10'])).
% 0.55/0.72  thf('12', plain, ((v1_relat_1 @ sk_B)),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('13', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 0.55/0.72      inference('demod', [status(thm)], ['11', '12'])).
% 0.55/0.72  thf('14', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 0.55/0.72      inference('demod', [status(thm)], ['11', '12'])).
% 0.55/0.72  thf('15', plain,
% 0.55/0.72      (![X11 : $i]:
% 0.55/0.72         (((k3_relat_1 @ X11)
% 0.55/0.72            = (k2_xboole_0 @ (k1_relat_1 @ X11) @ (k2_relat_1 @ X11)))
% 0.55/0.72          | ~ (v1_relat_1 @ X11))),
% 0.55/0.72      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.55/0.72  thf(t7_xboole_1, axiom,
% 0.55/0.72    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.55/0.72  thf('16', plain,
% 0.55/0.72      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 0.55/0.72      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.55/0.72  thf('17', plain,
% 0.55/0.72      (![X0 : $i]:
% 0.55/0.72         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 0.55/0.72          | ~ (v1_relat_1 @ X0))),
% 0.55/0.72      inference('sup+', [status(thm)], ['15', '16'])).
% 0.55/0.72  thf(t8_xboole_1, axiom,
% 0.55/0.72    (![A:$i,B:$i,C:$i]:
% 0.55/0.72     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.55/0.72       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.55/0.72  thf('18', plain,
% 0.55/0.72      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.55/0.72         (~ (r1_tarski @ X8 @ X9)
% 0.55/0.72          | ~ (r1_tarski @ X10 @ X9)
% 0.55/0.72          | (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 0.55/0.72      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.55/0.72  thf('19', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i]:
% 0.55/0.72         (~ (v1_relat_1 @ X0)
% 0.55/0.72          | (r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ X0) @ X1) @ 
% 0.55/0.72             (k3_relat_1 @ X0))
% 0.55/0.72          | ~ (r1_tarski @ X1 @ (k3_relat_1 @ X0)))),
% 0.55/0.72      inference('sup-', [status(thm)], ['17', '18'])).
% 0.55/0.72  thf('20', plain,
% 0.55/0.72      (((r1_tarski @ 
% 0.55/0.72         (k2_xboole_0 @ (k1_relat_1 @ sk_B) @ (k2_relat_1 @ sk_A)) @ 
% 0.55/0.72         (k3_relat_1 @ sk_B))
% 0.55/0.72        | ~ (v1_relat_1 @ sk_B))),
% 0.55/0.72      inference('sup-', [status(thm)], ['14', '19'])).
% 0.55/0.72  thf('21', plain, ((v1_relat_1 @ sk_B)),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('22', plain,
% 0.55/0.72      ((r1_tarski @ 
% 0.55/0.72        (k2_xboole_0 @ (k1_relat_1 @ sk_B) @ (k2_relat_1 @ sk_A)) @ 
% 0.55/0.72        (k3_relat_1 @ sk_B))),
% 0.55/0.72      inference('demod', [status(thm)], ['20', '21'])).
% 0.55/0.72  thf('23', plain,
% 0.55/0.72      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 0.55/0.72      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.55/0.72  thf(t1_xboole_1, axiom,
% 0.55/0.72    (![A:$i,B:$i,C:$i]:
% 0.55/0.72     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.55/0.72       ( r1_tarski @ A @ C ) ))).
% 0.55/0.72  thf('24', plain,
% 0.55/0.72      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.55/0.72         (~ (r1_tarski @ X3 @ X4)
% 0.55/0.72          | ~ (r1_tarski @ X4 @ X5)
% 0.55/0.72          | (r1_tarski @ X3 @ X5))),
% 0.55/0.72      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.55/0.72  thf('25', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.72         ((r1_tarski @ X1 @ X2) | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 0.55/0.72      inference('sup-', [status(thm)], ['23', '24'])).
% 0.55/0.72  thf('26', plain, ((r1_tarski @ (k1_relat_1 @ sk_B) @ (k3_relat_1 @ sk_B))),
% 0.55/0.72      inference('sup-', [status(thm)], ['22', '25'])).
% 0.55/0.72  thf('27', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('28', plain,
% 0.55/0.72      (![X12 : $i, X13 : $i]:
% 0.55/0.72         (~ (v1_relat_1 @ X12)
% 0.55/0.72          | (r1_tarski @ (k1_relat_1 @ X13) @ (k1_relat_1 @ X12))
% 0.55/0.72          | ~ (r1_tarski @ X13 @ X12)
% 0.55/0.72          | ~ (v1_relat_1 @ X13))),
% 0.55/0.72      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.55/0.72  thf('29', plain,
% 0.55/0.72      ((~ (v1_relat_1 @ sk_A)
% 0.55/0.72        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 0.55/0.72        | ~ (v1_relat_1 @ sk_B))),
% 0.55/0.72      inference('sup-', [status(thm)], ['27', '28'])).
% 0.55/0.72  thf('30', plain, ((v1_relat_1 @ sk_A)),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('31', plain, ((v1_relat_1 @ sk_B)),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('32', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))),
% 0.55/0.72      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.55/0.72  thf('33', plain,
% 0.55/0.72      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.55/0.72         (~ (r1_tarski @ X3 @ X4)
% 0.55/0.72          | ~ (r1_tarski @ X4 @ X5)
% 0.55/0.72          | (r1_tarski @ X3 @ X5))),
% 0.55/0.72      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.55/0.72  thf('34', plain,
% 0.55/0.72      (![X0 : $i]:
% 0.55/0.72         ((r1_tarski @ (k1_relat_1 @ sk_A) @ X0)
% 0.55/0.72          | ~ (r1_tarski @ (k1_relat_1 @ sk_B) @ X0))),
% 0.55/0.72      inference('sup-', [status(thm)], ['32', '33'])).
% 0.55/0.72  thf('35', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 0.55/0.72      inference('sup-', [status(thm)], ['26', '34'])).
% 0.55/0.72  thf('36', plain,
% 0.55/0.72      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.55/0.72         (~ (r1_tarski @ X8 @ X9)
% 0.55/0.72          | ~ (r1_tarski @ X10 @ X9)
% 0.55/0.72          | (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 0.55/0.72      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.55/0.72  thf('37', plain,
% 0.55/0.72      (![X0 : $i]:
% 0.55/0.72         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 0.55/0.72           (k3_relat_1 @ sk_B))
% 0.55/0.72          | ~ (r1_tarski @ X0 @ (k3_relat_1 @ sk_B)))),
% 0.55/0.72      inference('sup-', [status(thm)], ['35', '36'])).
% 0.55/0.72  thf('38', plain,
% 0.55/0.72      ((r1_tarski @ 
% 0.55/0.72        (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)) @ 
% 0.55/0.72        (k3_relat_1 @ sk_B))),
% 0.55/0.72      inference('sup-', [status(thm)], ['13', '37'])).
% 0.55/0.72  thf('39', plain,
% 0.55/0.72      (((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))
% 0.55/0.72        | ~ (v1_relat_1 @ sk_A))),
% 0.55/0.72      inference('sup+', [status(thm)], ['1', '38'])).
% 0.55/0.72  thf('40', plain, ((v1_relat_1 @ sk_A)),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('41', plain, ((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 0.55/0.72      inference('demod', [status(thm)], ['39', '40'])).
% 0.55/0.72  thf('42', plain, ($false), inference('demod', [status(thm)], ['0', '41'])).
% 0.55/0.72  
% 0.55/0.72  % SZS output end Refutation
% 0.55/0.72  
% 0.55/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
