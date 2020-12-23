%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1PkLmxus9P

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:59 EST 2020

% Result     : Theorem 1.00s
% Output     : Refutation 1.00s
% Verified   : 
% Statistics : Number of formulae       :   59 (  84 expanded)
%              Number of leaves         :   17 (  31 expanded)
%              Depth                    :   12
%              Number of atoms          :  381 ( 646 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('5',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t26_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k2_xboole_0 @ A @ B ) )
            = ( k2_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( ( k2_relat_1 @ ( k2_xboole_0 @ X17 @ X16 ) )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X17 ) @ ( k2_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t26_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X13: $i] :
      ( ( ( k3_relat_1 @ X13 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X13 ) @ ( k2_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('19',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t13_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k2_xboole_0 @ A @ B ) )
            = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('22',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k1_relat_1 @ ( k2_xboole_0 @ X15 @ X14 ) )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X15 ) @ ( k1_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t13_relat_1])).

thf('23',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('24',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('34',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X12 @ X11 )
      | ( r1_tarski @ ( k2_xboole_0 @ X10 @ X12 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k3_relat_1 @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( k3_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['17','35'])).

thf('37',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['0','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1PkLmxus9P
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:39:37 EST 2020
% 0.21/0.34  % CPUTime    : 
% 0.21/0.34  % Running portfolio for 600 s
% 0.21/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.21/0.34  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 1.00/1.18  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.00/1.18  % Solved by: fo/fo7.sh
% 1.00/1.18  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.00/1.18  % done 1221 iterations in 0.729s
% 1.00/1.18  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.00/1.18  % SZS output start Refutation
% 1.00/1.18  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.00/1.18  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.00/1.18  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.00/1.18  thf(sk_B_type, type, sk_B: $i).
% 1.00/1.18  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.00/1.18  thf(sk_A_type, type, sk_A: $i).
% 1.00/1.18  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.00/1.18  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 1.00/1.18  thf(t31_relat_1, conjecture,
% 1.00/1.18    (![A:$i]:
% 1.00/1.18     ( ( v1_relat_1 @ A ) =>
% 1.00/1.18       ( ![B:$i]:
% 1.00/1.18         ( ( v1_relat_1 @ B ) =>
% 1.00/1.18           ( ( r1_tarski @ A @ B ) =>
% 1.00/1.18             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 1.00/1.18  thf(zf_stmt_0, negated_conjecture,
% 1.00/1.18    (~( ![A:$i]:
% 1.00/1.18        ( ( v1_relat_1 @ A ) =>
% 1.00/1.18          ( ![B:$i]:
% 1.00/1.18            ( ( v1_relat_1 @ B ) =>
% 1.00/1.18              ( ( r1_tarski @ A @ B ) =>
% 1.00/1.18                ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 1.00/1.18    inference('cnf.neg', [status(esa)], [t31_relat_1])).
% 1.00/1.18  thf('0', plain, (~ (r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf(d6_relat_1, axiom,
% 1.00/1.18    (![A:$i]:
% 1.00/1.18     ( ( v1_relat_1 @ A ) =>
% 1.00/1.18       ( ( k3_relat_1 @ A ) =
% 1.00/1.18         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 1.00/1.18  thf('1', plain,
% 1.00/1.18      (![X13 : $i]:
% 1.00/1.18         (((k3_relat_1 @ X13)
% 1.00/1.18            = (k2_xboole_0 @ (k1_relat_1 @ X13) @ (k2_relat_1 @ X13)))
% 1.00/1.18          | ~ (v1_relat_1 @ X13))),
% 1.00/1.18      inference('cnf', [status(esa)], [d6_relat_1])).
% 1.00/1.18  thf('2', plain,
% 1.00/1.18      (![X13 : $i]:
% 1.00/1.18         (((k3_relat_1 @ X13)
% 1.00/1.18            = (k2_xboole_0 @ (k1_relat_1 @ X13) @ (k2_relat_1 @ X13)))
% 1.00/1.18          | ~ (v1_relat_1 @ X13))),
% 1.00/1.18      inference('cnf', [status(esa)], [d6_relat_1])).
% 1.00/1.18  thf('3', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf(t12_xboole_1, axiom,
% 1.00/1.18    (![A:$i,B:$i]:
% 1.00/1.18     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.00/1.18  thf('4', plain,
% 1.00/1.18      (![X3 : $i, X4 : $i]:
% 1.00/1.18         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 1.00/1.18      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.00/1.18  thf('5', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 1.00/1.18      inference('sup-', [status(thm)], ['3', '4'])).
% 1.00/1.18  thf(t26_relat_1, axiom,
% 1.00/1.18    (![A:$i]:
% 1.00/1.18     ( ( v1_relat_1 @ A ) =>
% 1.00/1.18       ( ![B:$i]:
% 1.00/1.18         ( ( v1_relat_1 @ B ) =>
% 1.00/1.18           ( ( k2_relat_1 @ ( k2_xboole_0 @ A @ B ) ) =
% 1.00/1.18             ( k2_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 1.00/1.18  thf('6', plain,
% 1.00/1.18      (![X16 : $i, X17 : $i]:
% 1.00/1.18         (~ (v1_relat_1 @ X16)
% 1.00/1.18          | ((k2_relat_1 @ (k2_xboole_0 @ X17 @ X16))
% 1.00/1.18              = (k2_xboole_0 @ (k2_relat_1 @ X17) @ (k2_relat_1 @ X16)))
% 1.00/1.18          | ~ (v1_relat_1 @ X17))),
% 1.00/1.18      inference('cnf', [status(esa)], [t26_relat_1])).
% 1.00/1.18  thf(t7_xboole_1, axiom,
% 1.00/1.18    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.00/1.18  thf('7', plain,
% 1.00/1.18      (![X8 : $i, X9 : $i]: (r1_tarski @ X8 @ (k2_xboole_0 @ X8 @ X9))),
% 1.00/1.18      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.00/1.18  thf('8', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i]:
% 1.00/1.18         ((r1_tarski @ (k2_relat_1 @ X1) @ 
% 1.00/1.18           (k2_relat_1 @ (k2_xboole_0 @ X1 @ X0)))
% 1.00/1.18          | ~ (v1_relat_1 @ X1)
% 1.00/1.18          | ~ (v1_relat_1 @ X0))),
% 1.00/1.18      inference('sup+', [status(thm)], ['6', '7'])).
% 1.00/1.18  thf('9', plain,
% 1.00/1.18      (((r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))
% 1.00/1.18        | ~ (v1_relat_1 @ sk_B)
% 1.00/1.18        | ~ (v1_relat_1 @ sk_A))),
% 1.00/1.18      inference('sup+', [status(thm)], ['5', '8'])).
% 1.00/1.18  thf('10', plain, ((v1_relat_1 @ sk_B)),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('11', plain, ((v1_relat_1 @ sk_A)),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('12', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))),
% 1.00/1.18      inference('demod', [status(thm)], ['9', '10', '11'])).
% 1.00/1.18  thf(t10_xboole_1, axiom,
% 1.00/1.18    (![A:$i,B:$i,C:$i]:
% 1.00/1.18     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 1.00/1.18  thf('13', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.18         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ X1)))),
% 1.00/1.18      inference('cnf', [status(esa)], [t10_xboole_1])).
% 1.00/1.18  thf('14', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         (r1_tarski @ (k2_relat_1 @ sk_A) @ 
% 1.00/1.18          (k2_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)))),
% 1.00/1.18      inference('sup-', [status(thm)], ['12', '13'])).
% 1.00/1.18  thf('15', plain,
% 1.00/1.18      (((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))
% 1.00/1.18        | ~ (v1_relat_1 @ sk_B))),
% 1.00/1.18      inference('sup+', [status(thm)], ['2', '14'])).
% 1.00/1.18  thf('16', plain, ((v1_relat_1 @ sk_B)),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('17', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 1.00/1.18      inference('demod', [status(thm)], ['15', '16'])).
% 1.00/1.18  thf('18', plain,
% 1.00/1.18      (![X13 : $i]:
% 1.00/1.18         (((k3_relat_1 @ X13)
% 1.00/1.18            = (k2_xboole_0 @ (k1_relat_1 @ X13) @ (k2_relat_1 @ X13)))
% 1.00/1.18          | ~ (v1_relat_1 @ X13))),
% 1.00/1.18      inference('cnf', [status(esa)], [d6_relat_1])).
% 1.00/1.18  thf('19', plain,
% 1.00/1.18      (![X8 : $i, X9 : $i]: (r1_tarski @ X8 @ (k2_xboole_0 @ X8 @ X9))),
% 1.00/1.18      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.00/1.18  thf('20', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 1.00/1.18          | ~ (v1_relat_1 @ X0))),
% 1.00/1.18      inference('sup+', [status(thm)], ['18', '19'])).
% 1.00/1.18  thf('21', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 1.00/1.18      inference('sup-', [status(thm)], ['3', '4'])).
% 1.00/1.18  thf(t13_relat_1, axiom,
% 1.00/1.18    (![A:$i]:
% 1.00/1.18     ( ( v1_relat_1 @ A ) =>
% 1.00/1.18       ( ![B:$i]:
% 1.00/1.18         ( ( v1_relat_1 @ B ) =>
% 1.00/1.18           ( ( k1_relat_1 @ ( k2_xboole_0 @ A @ B ) ) =
% 1.00/1.18             ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 1.00/1.18  thf('22', plain,
% 1.00/1.18      (![X14 : $i, X15 : $i]:
% 1.00/1.18         (~ (v1_relat_1 @ X14)
% 1.00/1.18          | ((k1_relat_1 @ (k2_xboole_0 @ X15 @ X14))
% 1.00/1.18              = (k2_xboole_0 @ (k1_relat_1 @ X15) @ (k1_relat_1 @ X14)))
% 1.00/1.18          | ~ (v1_relat_1 @ X15))),
% 1.00/1.18      inference('cnf', [status(esa)], [t13_relat_1])).
% 1.00/1.18  thf('23', plain,
% 1.00/1.18      (![X8 : $i, X9 : $i]: (r1_tarski @ X8 @ (k2_xboole_0 @ X8 @ X9))),
% 1.00/1.18      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.00/1.18  thf(t1_xboole_1, axiom,
% 1.00/1.18    (![A:$i,B:$i,C:$i]:
% 1.00/1.18     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.00/1.18       ( r1_tarski @ A @ C ) ))).
% 1.00/1.18  thf('24', plain,
% 1.00/1.18      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.00/1.18         (~ (r1_tarski @ X5 @ X6)
% 1.00/1.18          | ~ (r1_tarski @ X6 @ X7)
% 1.00/1.18          | (r1_tarski @ X5 @ X7))),
% 1.00/1.18      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.00/1.18  thf('25', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.18         ((r1_tarski @ X1 @ X2) | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 1.00/1.18      inference('sup-', [status(thm)], ['23', '24'])).
% 1.00/1.18  thf('26', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.18         (~ (r1_tarski @ (k1_relat_1 @ (k2_xboole_0 @ X1 @ X0)) @ X2)
% 1.00/1.18          | ~ (v1_relat_1 @ X1)
% 1.00/1.18          | ~ (v1_relat_1 @ X0)
% 1.00/1.18          | (r1_tarski @ (k1_relat_1 @ X1) @ X2))),
% 1.00/1.18      inference('sup-', [status(thm)], ['22', '25'])).
% 1.00/1.18  thf('27', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         (~ (r1_tarski @ (k1_relat_1 @ sk_B) @ X0)
% 1.00/1.18          | (r1_tarski @ (k1_relat_1 @ sk_A) @ X0)
% 1.00/1.18          | ~ (v1_relat_1 @ sk_B)
% 1.00/1.18          | ~ (v1_relat_1 @ sk_A))),
% 1.00/1.18      inference('sup-', [status(thm)], ['21', '26'])).
% 1.00/1.18  thf('28', plain, ((v1_relat_1 @ sk_B)),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('29', plain, ((v1_relat_1 @ sk_A)),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('30', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         (~ (r1_tarski @ (k1_relat_1 @ sk_B) @ X0)
% 1.00/1.18          | (r1_tarski @ (k1_relat_1 @ sk_A) @ X0))),
% 1.00/1.18      inference('demod', [status(thm)], ['27', '28', '29'])).
% 1.00/1.18  thf('31', plain,
% 1.00/1.18      ((~ (v1_relat_1 @ sk_B)
% 1.00/1.18        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 1.00/1.18      inference('sup-', [status(thm)], ['20', '30'])).
% 1.00/1.18  thf('32', plain, ((v1_relat_1 @ sk_B)),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('33', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 1.00/1.18      inference('demod', [status(thm)], ['31', '32'])).
% 1.00/1.18  thf(t8_xboole_1, axiom,
% 1.00/1.18    (![A:$i,B:$i,C:$i]:
% 1.00/1.18     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 1.00/1.18       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.00/1.18  thf('34', plain,
% 1.00/1.18      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.00/1.18         (~ (r1_tarski @ X10 @ X11)
% 1.00/1.18          | ~ (r1_tarski @ X12 @ X11)
% 1.00/1.18          | (r1_tarski @ (k2_xboole_0 @ X10 @ X12) @ X11))),
% 1.00/1.18      inference('cnf', [status(esa)], [t8_xboole_1])).
% 1.00/1.18  thf('35', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 1.00/1.18           (k3_relat_1 @ sk_B))
% 1.00/1.18          | ~ (r1_tarski @ X0 @ (k3_relat_1 @ sk_B)))),
% 1.00/1.18      inference('sup-', [status(thm)], ['33', '34'])).
% 1.00/1.18  thf('36', plain,
% 1.00/1.18      ((r1_tarski @ 
% 1.00/1.18        (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)) @ 
% 1.00/1.18        (k3_relat_1 @ sk_B))),
% 1.00/1.18      inference('sup-', [status(thm)], ['17', '35'])).
% 1.00/1.18  thf('37', plain,
% 1.00/1.18      (((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))
% 1.00/1.18        | ~ (v1_relat_1 @ sk_A))),
% 1.00/1.18      inference('sup+', [status(thm)], ['1', '36'])).
% 1.00/1.18  thf('38', plain, ((v1_relat_1 @ sk_A)),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('39', plain, ((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 1.00/1.18      inference('demod', [status(thm)], ['37', '38'])).
% 1.00/1.18  thf('40', plain, ($false), inference('demod', [status(thm)], ['0', '39'])).
% 1.00/1.18  
% 1.00/1.18  % SZS output end Refutation
% 1.00/1.18  
% 1.00/1.19  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
