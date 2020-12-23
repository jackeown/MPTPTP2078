%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2voEdISWwY

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:29 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   44 (  48 expanded)
%              Number of leaves         :   17 (  20 expanded)
%              Depth                    :   10
%              Number of atoms          :  300 ( 340 expanded)
%              Number of equality atoms :   50 (  56 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('0',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X14 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('6',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['4','9'])).

thf(t44_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( X28 = k1_xboole_0 )
      | ( X29 = k1_xboole_0 )
      | ( X28 = X29 )
      | ( ( k1_tarski @ X30 )
       != ( k2_xboole_0 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t44_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X2 )
       != X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( ( k4_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X2 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X2 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X2 )
        = ( k4_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('14',plain,(
    ! [X23: $i,X24: $i] :
      ( ( X24 != X23 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X24 ) @ ( k1_tarski @ X23 ) )
       != ( k1_tarski @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('15',plain,(
    ! [X23: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X23 ) @ ( k1_tarski @ X23 ) )
     != ( k1_tarski @ X23 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X23: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X23 ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X2 )
        = ( k4_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X2 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['13','19'])).

thf(t69_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
        | ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t69_zfmisc_1])).

thf('21',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2voEdISWwY
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:05:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.47/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.68  % Solved by: fo/fo7.sh
% 0.47/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.68  % done 698 iterations in 0.225s
% 0.47/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.68  % SZS output start Refutation
% 0.47/0.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.47/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.68  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.47/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.68  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.47/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.68  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.47/0.68  thf(t36_xboole_1, axiom,
% 0.47/0.68    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.47/0.68  thf('0', plain,
% 0.47/0.68      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 0.47/0.68      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.47/0.68  thf(l32_xboole_1, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.47/0.68  thf('1', plain,
% 0.47/0.68      (![X2 : $i, X4 : $i]:
% 0.47/0.68         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.47/0.68      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.47/0.68  thf('2', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]:
% 0.47/0.68         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['0', '1'])).
% 0.47/0.68  thf(t98_xboole_1, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.47/0.68  thf('3', plain,
% 0.47/0.68      (![X15 : $i, X16 : $i]:
% 0.47/0.68         ((k2_xboole_0 @ X15 @ X16)
% 0.47/0.68           = (k5_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15)))),
% 0.47/0.68      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.47/0.68  thf('4', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]:
% 0.47/0.68         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.47/0.68           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.47/0.68      inference('sup+', [status(thm)], ['2', '3'])).
% 0.47/0.68  thf(t4_boole, axiom,
% 0.47/0.68    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.47/0.68  thf('5', plain,
% 0.47/0.68      (![X14 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X14) = (k1_xboole_0))),
% 0.47/0.68      inference('cnf', [status(esa)], [t4_boole])).
% 0.47/0.68  thf('6', plain,
% 0.47/0.68      (![X15 : $i, X16 : $i]:
% 0.47/0.68         ((k2_xboole_0 @ X15 @ X16)
% 0.47/0.68           = (k5_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15)))),
% 0.47/0.68      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.47/0.68  thf('7', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.47/0.68      inference('sup+', [status(thm)], ['5', '6'])).
% 0.47/0.68  thf(t1_boole, axiom,
% 0.47/0.68    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.47/0.68  thf('8', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.47/0.68      inference('cnf', [status(esa)], [t1_boole])).
% 0.47/0.68  thf('9', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.47/0.68      inference('sup+', [status(thm)], ['7', '8'])).
% 0.47/0.68  thf('10', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]:
% 0.47/0.68         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.47/0.68      inference('demod', [status(thm)], ['4', '9'])).
% 0.47/0.68  thf(t44_zfmisc_1, axiom,
% 0.47/0.68    (![A:$i,B:$i,C:$i]:
% 0.47/0.68     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.47/0.68          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.47/0.68          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.47/0.68  thf('11', plain,
% 0.47/0.68      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.47/0.68         (((X28) = (k1_xboole_0))
% 0.47/0.68          | ((X29) = (k1_xboole_0))
% 0.47/0.68          | ((X28) = (X29))
% 0.47/0.68          | ((k1_tarski @ X30) != (k2_xboole_0 @ X28 @ X29)))),
% 0.47/0.68      inference('cnf', [status(esa)], [t44_zfmisc_1])).
% 0.47/0.68  thf('12', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.68         (((k1_tarski @ X2) != (X0))
% 0.47/0.68          | ((X0) = (k4_xboole_0 @ X0 @ X1))
% 0.47/0.68          | ((k4_xboole_0 @ X0 @ X1) = (k1_xboole_0))
% 0.47/0.68          | ((X0) = (k1_xboole_0)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['10', '11'])).
% 0.47/0.68  thf('13', plain,
% 0.47/0.68      (![X1 : $i, X2 : $i]:
% 0.47/0.68         (((k1_tarski @ X2) = (k1_xboole_0))
% 0.47/0.68          | ((k4_xboole_0 @ (k1_tarski @ X2) @ X1) = (k1_xboole_0))
% 0.47/0.68          | ((k1_tarski @ X2) = (k4_xboole_0 @ (k1_tarski @ X2) @ X1)))),
% 0.47/0.68      inference('simplify', [status(thm)], ['12'])).
% 0.47/0.68  thf(t20_zfmisc_1, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.47/0.68         ( k1_tarski @ A ) ) <=>
% 0.47/0.68       ( ( A ) != ( B ) ) ))).
% 0.47/0.68  thf('14', plain,
% 0.47/0.68      (![X23 : $i, X24 : $i]:
% 0.47/0.68         (((X24) != (X23))
% 0.47/0.68          | ((k4_xboole_0 @ (k1_tarski @ X24) @ (k1_tarski @ X23))
% 0.47/0.68              != (k1_tarski @ X24)))),
% 0.47/0.68      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.47/0.68  thf('15', plain,
% 0.47/0.68      (![X23 : $i]:
% 0.47/0.68         ((k4_xboole_0 @ (k1_tarski @ X23) @ (k1_tarski @ X23))
% 0.47/0.68           != (k1_tarski @ X23))),
% 0.47/0.68      inference('simplify', [status(thm)], ['14'])).
% 0.47/0.68  thf('16', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.47/0.68      inference('cnf', [status(esa)], [t1_boole])).
% 0.47/0.68  thf(t46_xboole_1, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.47/0.68  thf('17', plain,
% 0.47/0.68      (![X10 : $i, X11 : $i]:
% 0.47/0.68         ((k4_xboole_0 @ X10 @ (k2_xboole_0 @ X10 @ X11)) = (k1_xboole_0))),
% 0.47/0.68      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.47/0.68  thf('18', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.47/0.68      inference('sup+', [status(thm)], ['16', '17'])).
% 0.47/0.68  thf('19', plain, (![X23 : $i]: ((k1_xboole_0) != (k1_tarski @ X23))),
% 0.47/0.68      inference('demod', [status(thm)], ['15', '18'])).
% 0.47/0.68  thf('20', plain,
% 0.47/0.68      (![X1 : $i, X2 : $i]:
% 0.47/0.68         (((k1_tarski @ X2) = (k4_xboole_0 @ (k1_tarski @ X2) @ X1))
% 0.47/0.68          | ((k4_xboole_0 @ (k1_tarski @ X2) @ X1) = (k1_xboole_0)))),
% 0.47/0.68      inference('clc', [status(thm)], ['13', '19'])).
% 0.47/0.68  thf(t69_zfmisc_1, conjecture,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.47/0.68       ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) ))).
% 0.47/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.68    (~( ![A:$i,B:$i]:
% 0.47/0.68        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.47/0.68          ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) ) )),
% 0.47/0.68    inference('cnf.neg', [status(esa)], [t69_zfmisc_1])).
% 0.47/0.68  thf('21', plain,
% 0.47/0.68      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('22', plain,
% 0.47/0.68      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.47/0.68        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['20', '21'])).
% 0.47/0.68  thf('23', plain,
% 0.47/0.68      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.47/0.68      inference('simplify', [status(thm)], ['22'])).
% 0.47/0.68  thf('24', plain,
% 0.47/0.68      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('25', plain, ($false),
% 0.47/0.68      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.47/0.68  
% 0.47/0.68  % SZS output end Refutation
% 0.47/0.68  
% 0.47/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
