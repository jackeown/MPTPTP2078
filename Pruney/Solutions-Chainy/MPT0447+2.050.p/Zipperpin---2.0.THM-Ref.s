%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BgxLY7deEF

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:59 EST 2020

% Result     : Theorem 0.97s
% Output     : Refutation 0.97s
% Verified   : 
% Statistics : Number of formulae       :   54 (  75 expanded)
%              Number of leaves         :   16 (  28 expanded)
%              Depth                    :   13
%              Number of atoms          :  324 ( 577 expanded)
%              Number of equality atoms :    7 (   9 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    ! [X13: $i] :
      ( ( ( k3_relat_1 @ X13 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X13 ) @ ( k2_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('2',plain,(
    ! [X13: $i] :
      ( ( ( k3_relat_1 @ X13 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X13 ) @ ( k2_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( r1_tarski @ ( k2_relat_1 @ X15 ) @ ( k2_relat_1 @ X14 ) )
      | ~ ( r1_tarski @ X15 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
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
    ! [X13: $i] :
      ( ( ( k3_relat_1 @ X13 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X13 ) @ ( k2_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( r1_tarski @ ( k1_relat_1 @ X15 ) @ ( k1_relat_1 @ X14 ) )
      | ~ ( r1_tarski @ X15 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('23',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('24',plain,
    ( ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('25',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('30',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X12 @ X11 )
      | ( r1_tarski @ ( k2_xboole_0 @ X10 @ X12 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k3_relat_1 @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( k3_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','31'])).

thf('33',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['0','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BgxLY7deEF
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:42:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.97/1.17  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.97/1.17  % Solved by: fo/fo7.sh
% 0.97/1.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.97/1.17  % done 1431 iterations in 0.717s
% 0.97/1.17  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.97/1.17  % SZS output start Refutation
% 0.97/1.17  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.97/1.17  thf(sk_A_type, type, sk_A: $i).
% 0.97/1.17  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.97/1.17  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.97/1.17  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.97/1.17  thf(sk_B_type, type, sk_B: $i).
% 0.97/1.17  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.97/1.17  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.97/1.17  thf(t31_relat_1, conjecture,
% 0.97/1.17    (![A:$i]:
% 0.97/1.17     ( ( v1_relat_1 @ A ) =>
% 0.97/1.17       ( ![B:$i]:
% 0.97/1.17         ( ( v1_relat_1 @ B ) =>
% 0.97/1.17           ( ( r1_tarski @ A @ B ) =>
% 0.97/1.17             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 0.97/1.17  thf(zf_stmt_0, negated_conjecture,
% 0.97/1.17    (~( ![A:$i]:
% 0.97/1.17        ( ( v1_relat_1 @ A ) =>
% 0.97/1.17          ( ![B:$i]:
% 0.97/1.17            ( ( v1_relat_1 @ B ) =>
% 0.97/1.17              ( ( r1_tarski @ A @ B ) =>
% 0.97/1.17                ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 0.97/1.17    inference('cnf.neg', [status(esa)], [t31_relat_1])).
% 0.97/1.17  thf('0', plain, (~ (r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf(d6_relat_1, axiom,
% 0.97/1.17    (![A:$i]:
% 0.97/1.17     ( ( v1_relat_1 @ A ) =>
% 0.97/1.17       ( ( k3_relat_1 @ A ) =
% 0.97/1.17         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.97/1.17  thf('1', plain,
% 0.97/1.17      (![X13 : $i]:
% 0.97/1.17         (((k3_relat_1 @ X13)
% 0.97/1.17            = (k2_xboole_0 @ (k1_relat_1 @ X13) @ (k2_relat_1 @ X13)))
% 0.97/1.17          | ~ (v1_relat_1 @ X13))),
% 0.97/1.17      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.97/1.17  thf('2', plain,
% 0.97/1.17      (![X13 : $i]:
% 0.97/1.17         (((k3_relat_1 @ X13)
% 0.97/1.17            = (k2_xboole_0 @ (k1_relat_1 @ X13) @ (k2_relat_1 @ X13)))
% 0.97/1.17          | ~ (v1_relat_1 @ X13))),
% 0.97/1.17      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.97/1.17  thf('3', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf(t25_relat_1, axiom,
% 0.97/1.17    (![A:$i]:
% 0.97/1.17     ( ( v1_relat_1 @ A ) =>
% 0.97/1.17       ( ![B:$i]:
% 0.97/1.17         ( ( v1_relat_1 @ B ) =>
% 0.97/1.17           ( ( r1_tarski @ A @ B ) =>
% 0.97/1.17             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.97/1.17               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.97/1.17  thf('4', plain,
% 0.97/1.17      (![X14 : $i, X15 : $i]:
% 0.97/1.17         (~ (v1_relat_1 @ X14)
% 0.97/1.17          | (r1_tarski @ (k2_relat_1 @ X15) @ (k2_relat_1 @ X14))
% 0.97/1.17          | ~ (r1_tarski @ X15 @ X14)
% 0.97/1.17          | ~ (v1_relat_1 @ X15))),
% 0.97/1.17      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.97/1.17  thf('5', plain,
% 0.97/1.17      ((~ (v1_relat_1 @ sk_A)
% 0.97/1.17        | (r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))
% 0.97/1.17        | ~ (v1_relat_1 @ sk_B))),
% 0.97/1.17      inference('sup-', [status(thm)], ['3', '4'])).
% 0.97/1.17  thf('6', plain, ((v1_relat_1 @ sk_A)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('7', plain, ((v1_relat_1 @ sk_B)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('8', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))),
% 0.97/1.17      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.97/1.17  thf(t10_xboole_1, axiom,
% 0.97/1.17    (![A:$i,B:$i,C:$i]:
% 0.97/1.17     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.97/1.17  thf('9', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.17         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ X1)))),
% 0.97/1.17      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.97/1.17  thf('10', plain,
% 0.97/1.17      (![X0 : $i]:
% 0.97/1.17         (r1_tarski @ (k2_relat_1 @ sk_A) @ 
% 0.97/1.17          (k2_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['8', '9'])).
% 0.97/1.17  thf('11', plain,
% 0.97/1.17      (((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))
% 0.97/1.17        | ~ (v1_relat_1 @ sk_B))),
% 0.97/1.17      inference('sup+', [status(thm)], ['2', '10'])).
% 0.97/1.17  thf('12', plain, ((v1_relat_1 @ sk_B)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('13', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 0.97/1.17      inference('demod', [status(thm)], ['11', '12'])).
% 0.97/1.17  thf('14', plain,
% 0.97/1.17      (![X13 : $i]:
% 0.97/1.17         (((k3_relat_1 @ X13)
% 0.97/1.17            = (k2_xboole_0 @ (k1_relat_1 @ X13) @ (k2_relat_1 @ X13)))
% 0.97/1.17          | ~ (v1_relat_1 @ X13))),
% 0.97/1.17      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.97/1.17  thf(t7_xboole_1, axiom,
% 0.97/1.17    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.97/1.17  thf('15', plain,
% 0.97/1.17      (![X8 : $i, X9 : $i]: (r1_tarski @ X8 @ (k2_xboole_0 @ X8 @ X9))),
% 0.97/1.17      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.97/1.17  thf('16', plain,
% 0.97/1.17      (![X0 : $i]:
% 0.97/1.17         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 0.97/1.17          | ~ (v1_relat_1 @ X0))),
% 0.97/1.17      inference('sup+', [status(thm)], ['14', '15'])).
% 0.97/1.17  thf('17', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('18', plain,
% 0.97/1.17      (![X14 : $i, X15 : $i]:
% 0.97/1.17         (~ (v1_relat_1 @ X14)
% 0.97/1.17          | (r1_tarski @ (k1_relat_1 @ X15) @ (k1_relat_1 @ X14))
% 0.97/1.17          | ~ (r1_tarski @ X15 @ X14)
% 0.97/1.17          | ~ (v1_relat_1 @ X15))),
% 0.97/1.17      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.97/1.17  thf('19', plain,
% 0.97/1.17      ((~ (v1_relat_1 @ sk_A)
% 0.97/1.17        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 0.97/1.17        | ~ (v1_relat_1 @ sk_B))),
% 0.97/1.17      inference('sup-', [status(thm)], ['17', '18'])).
% 0.97/1.17  thf('20', plain, ((v1_relat_1 @ sk_A)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('21', plain, ((v1_relat_1 @ sk_B)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('22', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))),
% 0.97/1.17      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.97/1.17  thf(t12_xboole_1, axiom,
% 0.97/1.17    (![A:$i,B:$i]:
% 0.97/1.17     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.97/1.17  thf('23', plain,
% 0.97/1.17      (![X6 : $i, X7 : $i]:
% 0.97/1.17         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.97/1.17      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.97/1.17  thf('24', plain,
% 0.97/1.17      (((k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 0.97/1.17         = (k1_relat_1 @ sk_B))),
% 0.97/1.17      inference('sup-', [status(thm)], ['22', '23'])).
% 0.97/1.17  thf(t11_xboole_1, axiom,
% 0.97/1.17    (![A:$i,B:$i,C:$i]:
% 0.97/1.17     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.97/1.17  thf('25', plain,
% 0.97/1.17      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.97/1.17         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 0.97/1.17      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.97/1.17  thf('26', plain,
% 0.97/1.17      (![X0 : $i]:
% 0.97/1.17         (~ (r1_tarski @ (k1_relat_1 @ sk_B) @ X0)
% 0.97/1.17          | (r1_tarski @ (k1_relat_1 @ sk_A) @ X0))),
% 0.97/1.17      inference('sup-', [status(thm)], ['24', '25'])).
% 0.97/1.17  thf('27', plain,
% 0.97/1.17      ((~ (v1_relat_1 @ sk_B)
% 0.97/1.17        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['16', '26'])).
% 0.97/1.17  thf('28', plain, ((v1_relat_1 @ sk_B)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('29', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 0.97/1.17      inference('demod', [status(thm)], ['27', '28'])).
% 0.97/1.17  thf(t8_xboole_1, axiom,
% 0.97/1.17    (![A:$i,B:$i,C:$i]:
% 0.97/1.17     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.97/1.17       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.97/1.17  thf('30', plain,
% 0.97/1.17      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.97/1.17         (~ (r1_tarski @ X10 @ X11)
% 0.97/1.17          | ~ (r1_tarski @ X12 @ X11)
% 0.97/1.17          | (r1_tarski @ (k2_xboole_0 @ X10 @ X12) @ X11))),
% 0.97/1.17      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.97/1.17  thf('31', plain,
% 0.97/1.17      (![X0 : $i]:
% 0.97/1.17         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 0.97/1.17           (k3_relat_1 @ sk_B))
% 0.97/1.17          | ~ (r1_tarski @ X0 @ (k3_relat_1 @ sk_B)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['29', '30'])).
% 0.97/1.17  thf('32', plain,
% 0.97/1.17      ((r1_tarski @ 
% 0.97/1.17        (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)) @ 
% 0.97/1.17        (k3_relat_1 @ sk_B))),
% 0.97/1.17      inference('sup-', [status(thm)], ['13', '31'])).
% 0.97/1.17  thf('33', plain,
% 0.97/1.17      (((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))
% 0.97/1.17        | ~ (v1_relat_1 @ sk_A))),
% 0.97/1.17      inference('sup+', [status(thm)], ['1', '32'])).
% 0.97/1.17  thf('34', plain, ((v1_relat_1 @ sk_A)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('35', plain, ((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 0.97/1.17      inference('demod', [status(thm)], ['33', '34'])).
% 0.97/1.17  thf('36', plain, ($false), inference('demod', [status(thm)], ['0', '35'])).
% 0.97/1.17  
% 0.97/1.17  % SZS output end Refutation
% 0.97/1.17  
% 0.97/1.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
