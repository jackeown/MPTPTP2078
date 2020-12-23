%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.x4OmUqelAK

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:58 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   52 (  62 expanded)
%              Number of leaves         :   20 (  27 expanded)
%              Depth                    :   12
%              Number of atoms          :  292 ( 369 expanded)
%              Number of equality atoms :   32 (  44 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(t21_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = k1_xboole_0 )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = k1_xboole_0 )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t21_zfmisc_1])).

thf('0',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ X13 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ X13 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf('12',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','11'])).

thf('13',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('14',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('15',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X47 ) @ X48 )
      | ( r2_hidden @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('16',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('17',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( v1_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['14','19'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('21',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( X15 != X14 )
      | ( r2_hidden @ X15 @ X16 )
      | ( X16
       != ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('22',plain,(
    ! [X14: $i] :
      ( r2_hidden @ X14 @ ( k1_tarski @ X14 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference(clc,[status(thm)],['20','24'])).

thf('26',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X17 @ X16 )
      | ( X17 = X14 )
      | ( X16
       != ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('27',plain,(
    ! [X14: $i,X17: $i] :
      ( ( X17 = X14 )
      | ~ ( r2_hidden @ X17 @ ( k1_tarski @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    sk_A = sk_B_1 ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.x4OmUqelAK
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:29:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.38/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.56  % Solved by: fo/fo7.sh
% 0.38/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.56  % done 77 iterations in 0.061s
% 0.38/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.56  % SZS output start Refutation
% 0.38/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.38/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.38/0.56  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.38/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.38/0.56  thf(t21_zfmisc_1, conjecture,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.38/0.56         ( k1_xboole_0 ) ) =>
% 0.38/0.56       ( ( A ) = ( B ) ) ))).
% 0.38/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.56    (~( ![A:$i,B:$i]:
% 0.38/0.56        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.38/0.56            ( k1_xboole_0 ) ) =>
% 0.38/0.56          ( ( A ) = ( B ) ) ) )),
% 0.38/0.56    inference('cnf.neg', [status(esa)], [t21_zfmisc_1])).
% 0.38/0.56  thf('0', plain,
% 0.38/0.56      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.38/0.56         = (k1_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(t100_xboole_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.38/0.56  thf('1', plain,
% 0.38/0.56      (![X7 : $i, X8 : $i]:
% 0.38/0.56         ((k4_xboole_0 @ X7 @ X8)
% 0.38/0.56           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.38/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.56  thf(t92_xboole_1, axiom,
% 0.38/0.56    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.38/0.56  thf('2', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ X13) = (k1_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.38/0.56  thf(t91_xboole_1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.38/0.56       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.38/0.56  thf('3', plain,
% 0.38/0.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.38/0.56         ((k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ X12)
% 0.38/0.56           = (k5_xboole_0 @ X10 @ (k5_xboole_0 @ X11 @ X12)))),
% 0.38/0.56      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.38/0.56  thf('4', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.38/0.56           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.38/0.56      inference('sup+', [status(thm)], ['2', '3'])).
% 0.38/0.56  thf('5', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ X13) = (k1_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.38/0.56  thf('6', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.38/0.56           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.38/0.56      inference('sup+', [status(thm)], ['2', '3'])).
% 0.38/0.56  thf('7', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.38/0.56      inference('sup+', [status(thm)], ['5', '6'])).
% 0.38/0.56  thf(t5_boole, axiom,
% 0.38/0.56    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.38/0.56  thf('8', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.38/0.56      inference('cnf', [status(esa)], [t5_boole])).
% 0.38/0.56  thf('9', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.38/0.56      inference('demod', [status(thm)], ['7', '8'])).
% 0.38/0.56  thf('10', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.38/0.56      inference('demod', [status(thm)], ['4', '9'])).
% 0.38/0.56  thf('11', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((k3_xboole_0 @ X1 @ X0)
% 0.38/0.56           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.38/0.56      inference('sup+', [status(thm)], ['1', '10'])).
% 0.38/0.56  thf('12', plain,
% 0.38/0.56      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.38/0.56         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0))),
% 0.38/0.56      inference('sup+', [status(thm)], ['0', '11'])).
% 0.38/0.56  thf('13', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.38/0.56      inference('cnf', [status(esa)], [t5_boole])).
% 0.38/0.56  thf('14', plain,
% 0.38/0.56      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.38/0.56         = (k1_tarski @ sk_A))),
% 0.38/0.56      inference('demod', [status(thm)], ['12', '13'])).
% 0.38/0.56  thf(l27_zfmisc_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.38/0.56  thf('15', plain,
% 0.38/0.56      (![X47 : $i, X48 : $i]:
% 0.38/0.56         ((r1_xboole_0 @ (k1_tarski @ X47) @ X48) | (r2_hidden @ X47 @ X48))),
% 0.38/0.56      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.38/0.56  thf(d1_xboole_0, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.38/0.56  thf('16', plain,
% 0.38/0.56      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.38/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.38/0.56  thf(t4_xboole_0, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.38/0.56            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.38/0.56       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.38/0.56            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.38/0.56  thf('17', plain,
% 0.38/0.56      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.38/0.56          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.38/0.56      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.38/0.56  thf('18', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['16', '17'])).
% 0.38/0.56  thf('19', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((r2_hidden @ X1 @ X0)
% 0.38/0.56          | (v1_xboole_0 @ (k3_xboole_0 @ (k1_tarski @ X1) @ X0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['15', '18'])).
% 0.38/0.56  thf('20', plain,
% 0.38/0.56      (((v1_xboole_0 @ (k1_tarski @ sk_A))
% 0.38/0.56        | (r2_hidden @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.38/0.56      inference('sup+', [status(thm)], ['14', '19'])).
% 0.38/0.56  thf(d1_tarski, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.38/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.38/0.56  thf('21', plain,
% 0.38/0.56      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.38/0.56         (((X15) != (X14))
% 0.38/0.56          | (r2_hidden @ X15 @ X16)
% 0.38/0.56          | ((X16) != (k1_tarski @ X14)))),
% 0.38/0.56      inference('cnf', [status(esa)], [d1_tarski])).
% 0.38/0.56  thf('22', plain, (![X14 : $i]: (r2_hidden @ X14 @ (k1_tarski @ X14))),
% 0.38/0.56      inference('simplify', [status(thm)], ['21'])).
% 0.38/0.56  thf('23', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.38/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.38/0.56  thf('24', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['22', '23'])).
% 0.38/0.56  thf('25', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.38/0.56      inference('clc', [status(thm)], ['20', '24'])).
% 0.38/0.56  thf('26', plain,
% 0.38/0.56      (![X14 : $i, X16 : $i, X17 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X17 @ X16)
% 0.38/0.56          | ((X17) = (X14))
% 0.38/0.56          | ((X16) != (k1_tarski @ X14)))),
% 0.38/0.56      inference('cnf', [status(esa)], [d1_tarski])).
% 0.38/0.56  thf('27', plain,
% 0.38/0.56      (![X14 : $i, X17 : $i]:
% 0.38/0.56         (((X17) = (X14)) | ~ (r2_hidden @ X17 @ (k1_tarski @ X14)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['26'])).
% 0.38/0.56  thf('28', plain, (((sk_A) = (sk_B_1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['25', '27'])).
% 0.38/0.56  thf('29', plain, (((sk_A) != (sk_B_1))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('30', plain, ($false),
% 0.38/0.56      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 0.38/0.56  
% 0.38/0.56  % SZS output end Refutation
% 0.38/0.56  
% 0.38/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
