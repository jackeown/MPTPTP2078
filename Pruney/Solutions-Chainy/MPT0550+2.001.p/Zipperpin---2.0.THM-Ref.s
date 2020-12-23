%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SnETML3pkf

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:18 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :   57 (  76 expanded)
%              Number of leaves         :   23 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :  301 ( 514 expanded)
%              Number of equality atoms :   32 (  60 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t152_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( A != k1_xboole_0 )
          & ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( ( k9_relat_1 @ B @ A )
            = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ~ ( ( A != k1_xboole_0 )
            & ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
            & ( ( k9_relat_1 @ B @ A )
              = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t152_relat_1])).

thf('3',plain,(
    r1_tarski @ sk_A_1 @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X16 @ ( k1_relat_1 @ X17 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('5',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A_1 ) )
      = sk_A_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A_1 ) )
    = sk_A_1 ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k1_xboole_0 = sk_A_1 )
    | ~ ( v1_xboole_0 @ ( k7_relat_1 @ sk_B @ sk_A_1 ) ) ),
    inference('sup+',[status(thm)],['2','7'])).

thf('9',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ~ ( v1_xboole_0 @ ( k7_relat_1 @ sk_B @ sk_A_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A_1 ) )
    = sk_A_1 ),
    inference(demod,[status(thm)],['5','6'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('13',plain,(
    ! [X13: $i] :
      ( ( r1_tarski @ X13 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X13 ) @ ( k2_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r1_tarski @ ( k7_relat_1 @ sk_B @ sk_A_1 ) @ ( k2_zfmisc_1 @ sk_A_1 @ ( k9_relat_1 @ sk_B @ sk_A_1 ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','16'])).

thf('18',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A_1 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('19',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('20',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    r1_tarski @ ( k7_relat_1 @ sk_B @ sk_A_1 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['17','18','20','21'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('23',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k7_relat_1 @ sk_B @ sk_A_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['22','25'])).

thf(rc1_xboole_0,axiom,(
    ? [A: $i] :
      ( v1_xboole_0 @ A ) )).

thf('27',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('28',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('30',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,(
    $false ),
    inference(demod,[status(thm)],['10','26','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SnETML3pkf
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:23:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.90/1.16  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.90/1.16  % Solved by: fo/fo7.sh
% 0.90/1.16  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.16  % done 1083 iterations in 0.704s
% 0.90/1.16  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.90/1.16  % SZS output start Refutation
% 0.90/1.16  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.90/1.16  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.90/1.16  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.90/1.16  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.90/1.16  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.16  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.90/1.16  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.90/1.16  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.90/1.16  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.16  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.90/1.16  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.90/1.16  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.16  thf(l13_xboole_0, axiom,
% 0.90/1.16    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.90/1.16  thf('0', plain,
% 0.90/1.16      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.16      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.90/1.16  thf(t60_relat_1, axiom,
% 0.90/1.16    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.90/1.16     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.90/1.16  thf('1', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.90/1.16      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.90/1.16  thf('2', plain,
% 0.90/1.16      (![X0 : $i]: (((k1_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.16      inference('sup+', [status(thm)], ['0', '1'])).
% 0.90/1.16  thf(t152_relat_1, conjecture,
% 0.90/1.16    (![A:$i,B:$i]:
% 0.90/1.16     ( ( v1_relat_1 @ B ) =>
% 0.90/1.16       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.90/1.16            ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & 
% 0.90/1.16            ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.90/1.16  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.16    (~( ![A:$i,B:$i]:
% 0.90/1.16        ( ( v1_relat_1 @ B ) =>
% 0.90/1.16          ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.90/1.16               ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & 
% 0.90/1.16               ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.90/1.16    inference('cnf.neg', [status(esa)], [t152_relat_1])).
% 0.90/1.16  thf('3', plain, ((r1_tarski @ sk_A_1 @ (k1_relat_1 @ sk_B))),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf(t91_relat_1, axiom,
% 0.90/1.16    (![A:$i,B:$i]:
% 0.90/1.16     ( ( v1_relat_1 @ B ) =>
% 0.90/1.16       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.90/1.16         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.90/1.16  thf('4', plain,
% 0.90/1.16      (![X16 : $i, X17 : $i]:
% 0.90/1.16         (~ (r1_tarski @ X16 @ (k1_relat_1 @ X17))
% 0.90/1.16          | ((k1_relat_1 @ (k7_relat_1 @ X17 @ X16)) = (X16))
% 0.90/1.16          | ~ (v1_relat_1 @ X17))),
% 0.90/1.16      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.90/1.16  thf('5', plain,
% 0.90/1.16      ((~ (v1_relat_1 @ sk_B)
% 0.90/1.16        | ((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A_1)) = (sk_A_1)))),
% 0.90/1.16      inference('sup-', [status(thm)], ['3', '4'])).
% 0.90/1.16  thf('6', plain, ((v1_relat_1 @ sk_B)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('7', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A_1)) = (sk_A_1))),
% 0.90/1.16      inference('demod', [status(thm)], ['5', '6'])).
% 0.90/1.16  thf('8', plain,
% 0.90/1.16      ((((k1_xboole_0) = (sk_A_1))
% 0.90/1.16        | ~ (v1_xboole_0 @ (k7_relat_1 @ sk_B @ sk_A_1)))),
% 0.90/1.16      inference('sup+', [status(thm)], ['2', '7'])).
% 0.90/1.16  thf('9', plain, (((sk_A_1) != (k1_xboole_0))),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('10', plain, (~ (v1_xboole_0 @ (k7_relat_1 @ sk_B @ sk_A_1))),
% 0.90/1.16      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.90/1.16  thf('11', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A_1)) = (sk_A_1))),
% 0.90/1.16      inference('demod', [status(thm)], ['5', '6'])).
% 0.90/1.16  thf(t148_relat_1, axiom,
% 0.90/1.16    (![A:$i,B:$i]:
% 0.90/1.16     ( ( v1_relat_1 @ B ) =>
% 0.90/1.16       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.90/1.16  thf('12', plain,
% 0.90/1.16      (![X11 : $i, X12 : $i]:
% 0.90/1.16         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 0.90/1.16          | ~ (v1_relat_1 @ X11))),
% 0.90/1.16      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.90/1.16  thf(t21_relat_1, axiom,
% 0.90/1.16    (![A:$i]:
% 0.90/1.16     ( ( v1_relat_1 @ A ) =>
% 0.90/1.16       ( r1_tarski @
% 0.90/1.16         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.90/1.16  thf('13', plain,
% 0.90/1.16      (![X13 : $i]:
% 0.90/1.16         ((r1_tarski @ X13 @ 
% 0.90/1.16           (k2_zfmisc_1 @ (k1_relat_1 @ X13) @ (k2_relat_1 @ X13)))
% 0.90/1.16          | ~ (v1_relat_1 @ X13))),
% 0.90/1.16      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.90/1.16  thf('14', plain,
% 0.90/1.16      (![X0 : $i, X1 : $i]:
% 0.90/1.16         ((r1_tarski @ (k7_relat_1 @ X1 @ X0) @ 
% 0.90/1.16           (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 0.90/1.16            (k9_relat_1 @ X1 @ X0)))
% 0.90/1.16          | ~ (v1_relat_1 @ X1)
% 0.90/1.16          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.90/1.16      inference('sup+', [status(thm)], ['12', '13'])).
% 0.90/1.16  thf(dt_k7_relat_1, axiom,
% 0.90/1.16    (![A:$i,B:$i]:
% 0.90/1.16     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.90/1.16  thf('15', plain,
% 0.90/1.16      (![X9 : $i, X10 : $i]:
% 0.90/1.16         (~ (v1_relat_1 @ X9) | (v1_relat_1 @ (k7_relat_1 @ X9 @ X10)))),
% 0.90/1.16      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.90/1.16  thf('16', plain,
% 0.90/1.16      (![X0 : $i, X1 : $i]:
% 0.90/1.16         (~ (v1_relat_1 @ X1)
% 0.90/1.16          | (r1_tarski @ (k7_relat_1 @ X1 @ X0) @ 
% 0.90/1.16             (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 0.90/1.16              (k9_relat_1 @ X1 @ X0))))),
% 0.90/1.16      inference('clc', [status(thm)], ['14', '15'])).
% 0.90/1.16  thf('17', plain,
% 0.90/1.16      (((r1_tarski @ (k7_relat_1 @ sk_B @ sk_A_1) @ 
% 0.90/1.16         (k2_zfmisc_1 @ sk_A_1 @ (k9_relat_1 @ sk_B @ sk_A_1)))
% 0.90/1.16        | ~ (v1_relat_1 @ sk_B))),
% 0.90/1.16      inference('sup+', [status(thm)], ['11', '16'])).
% 0.90/1.16  thf('18', plain, (((k9_relat_1 @ sk_B @ sk_A_1) = (k1_xboole_0))),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf(t113_zfmisc_1, axiom,
% 0.90/1.16    (![A:$i,B:$i]:
% 0.90/1.16     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.90/1.16       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.90/1.16  thf('19', plain,
% 0.90/1.16      (![X6 : $i, X7 : $i]:
% 0.90/1.16         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 0.90/1.16      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.90/1.16  thf('20', plain,
% 0.90/1.16      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.90/1.16      inference('simplify', [status(thm)], ['19'])).
% 0.90/1.16  thf('21', plain, ((v1_relat_1 @ sk_B)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('22', plain, ((r1_tarski @ (k7_relat_1 @ sk_B @ sk_A_1) @ k1_xboole_0)),
% 0.90/1.16      inference('demod', [status(thm)], ['17', '18', '20', '21'])).
% 0.90/1.16  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.90/1.16  thf('23', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.90/1.16      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.90/1.16  thf(d10_xboole_0, axiom,
% 0.90/1.16    (![A:$i,B:$i]:
% 0.90/1.16     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.90/1.16  thf('24', plain,
% 0.90/1.16      (![X1 : $i, X3 : $i]:
% 0.90/1.16         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.90/1.16      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.16  thf('25', plain,
% 0.90/1.16      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.90/1.16      inference('sup-', [status(thm)], ['23', '24'])).
% 0.90/1.16  thf('26', plain, (((k7_relat_1 @ sk_B @ sk_A_1) = (k1_xboole_0))),
% 0.90/1.16      inference('sup-', [status(thm)], ['22', '25'])).
% 0.90/1.16  thf(rc1_xboole_0, axiom, (?[A:$i]: ( v1_xboole_0 @ A ))).
% 0.90/1.16  thf('27', plain, ((v1_xboole_0 @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.90/1.16  thf('28', plain, ((v1_xboole_0 @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.90/1.16  thf('29', plain,
% 0.90/1.16      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.16      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.90/1.16  thf('30', plain, (((sk_A) = (k1_xboole_0))),
% 0.90/1.16      inference('sup-', [status(thm)], ['28', '29'])).
% 0.90/1.16  thf('31', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.90/1.16      inference('demod', [status(thm)], ['27', '30'])).
% 0.90/1.16  thf('32', plain, ($false),
% 0.90/1.16      inference('demod', [status(thm)], ['10', '26', '31'])).
% 0.90/1.16  
% 0.90/1.16  % SZS output end Refutation
% 0.90/1.16  
% 0.90/1.16  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
