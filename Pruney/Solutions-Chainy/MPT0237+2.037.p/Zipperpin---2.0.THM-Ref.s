%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.x4ciEHQ8fT

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:03 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   54 (  83 expanded)
%              Number of leaves         :   21 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :  346 ( 616 expanded)
%              Number of equality atoms :   47 (  84 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t32_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t32_zfmisc_1])).

thf('0',plain,(
    ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X34 @ X35 ) )
      = ( k2_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('2',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t29_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k2_tarski @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k5_xboole_0 @ ( k1_tarski @ X40 ) @ ( k1_tarski @ X41 ) )
        = ( k2_tarski @ X40 @ X41 ) )
      | ( X40 = X41 ) ) ),
    inference(cnf,[status(esa)],[t29_zfmisc_1])).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('4',plain,(
    ! [X38: $i,X39: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X38 ) @ ( k1_tarski @ X39 ) )
      | ( X38 = X39 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X1 = X0 )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('12',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['12'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('14',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('15',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('16',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X36: $i,X37: $i] :
      ( r1_tarski @ ( k1_tarski @ X36 ) @ ( k2_tarski @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k5_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('24',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','25'])).

thf('27',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('28',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['12'])).

thf('29',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('30',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['2','13','26','27','28','29'])).

thf('31',plain,(
    $false ),
    inference(simplify,[status(thm)],['30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.x4ciEHQ8fT
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:26:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.56  % Solved by: fo/fo7.sh
% 0.35/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.56  % done 257 iterations in 0.110s
% 0.35/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.56  % SZS output start Refutation
% 0.35/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.35/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.56  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.35/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.35/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.35/0.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.35/0.56  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.35/0.56  thf(t32_zfmisc_1, conjecture,
% 0.35/0.56    (![A:$i,B:$i]:
% 0.35/0.56     ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 0.35/0.56       ( k2_tarski @ A @ B ) ))).
% 0.35/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.56    (~( ![A:$i,B:$i]:
% 0.35/0.56        ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 0.35/0.56          ( k2_tarski @ A @ B ) ) )),
% 0.35/0.56    inference('cnf.neg', [status(esa)], [t32_zfmisc_1])).
% 0.35/0.56  thf('0', plain,
% 0.35/0.56      (((k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 0.35/0.56         != (k2_tarski @ sk_A @ sk_B))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf(l51_zfmisc_1, axiom,
% 0.35/0.56    (![A:$i,B:$i]:
% 0.35/0.56     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.35/0.56  thf('1', plain,
% 0.35/0.56      (![X34 : $i, X35 : $i]:
% 0.35/0.56         ((k3_tarski @ (k2_tarski @ X34 @ X35)) = (k2_xboole_0 @ X34 @ X35))),
% 0.35/0.56      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.35/0.56  thf('2', plain,
% 0.35/0.56      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.35/0.56         != (k2_tarski @ sk_A @ sk_B))),
% 0.35/0.56      inference('demod', [status(thm)], ['0', '1'])).
% 0.35/0.56  thf(t29_zfmisc_1, axiom,
% 0.35/0.56    (![A:$i,B:$i]:
% 0.35/0.56     ( ( ( A ) != ( B ) ) =>
% 0.35/0.56       ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.35/0.56         ( k2_tarski @ A @ B ) ) ))).
% 0.35/0.56  thf('3', plain,
% 0.35/0.56      (![X40 : $i, X41 : $i]:
% 0.35/0.56         (((k5_xboole_0 @ (k1_tarski @ X40) @ (k1_tarski @ X41))
% 0.35/0.56            = (k2_tarski @ X40 @ X41))
% 0.35/0.56          | ((X40) = (X41)))),
% 0.35/0.56      inference('cnf', [status(esa)], [t29_zfmisc_1])).
% 0.35/0.56  thf(t17_zfmisc_1, axiom,
% 0.35/0.56    (![A:$i,B:$i]:
% 0.35/0.56     ( ( ( A ) != ( B ) ) =>
% 0.35/0.56       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.35/0.56  thf('4', plain,
% 0.35/0.56      (![X38 : $i, X39 : $i]:
% 0.35/0.56         ((r1_xboole_0 @ (k1_tarski @ X38) @ (k1_tarski @ X39))
% 0.35/0.56          | ((X38) = (X39)))),
% 0.35/0.56      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.35/0.56  thf(t83_xboole_1, axiom,
% 0.35/0.56    (![A:$i,B:$i]:
% 0.35/0.56     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.35/0.56  thf('5', plain,
% 0.35/0.56      (![X8 : $i, X9 : $i]:
% 0.35/0.56         (((k4_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 0.35/0.56      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.35/0.56  thf('6', plain,
% 0.35/0.56      (![X0 : $i, X1 : $i]:
% 0.35/0.56         (((X1) = (X0))
% 0.35/0.56          | ((k4_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.35/0.56              = (k1_tarski @ X1)))),
% 0.35/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.35/0.56  thf(t98_xboole_1, axiom,
% 0.35/0.56    (![A:$i,B:$i]:
% 0.35/0.56     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.35/0.56  thf('7', plain,
% 0.35/0.56      (![X11 : $i, X12 : $i]:
% 0.35/0.56         ((k2_xboole_0 @ X11 @ X12)
% 0.35/0.56           = (k5_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11)))),
% 0.35/0.56      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.35/0.56  thf('8', plain,
% 0.35/0.56      (![X0 : $i, X1 : $i]:
% 0.35/0.56         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.35/0.56            = (k5_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))
% 0.35/0.56          | ((X0) = (X1)))),
% 0.35/0.56      inference('sup+', [status(thm)], ['6', '7'])).
% 0.35/0.56  thf('9', plain,
% 0.35/0.56      (![X0 : $i, X1 : $i]:
% 0.35/0.56         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.35/0.56            = (k2_tarski @ X1 @ X0))
% 0.35/0.56          | ((X1) = (X0))
% 0.35/0.56          | ((X0) = (X1)))),
% 0.35/0.56      inference('sup+', [status(thm)], ['3', '8'])).
% 0.35/0.56  thf('10', plain,
% 0.35/0.56      (![X0 : $i, X1 : $i]:
% 0.35/0.56         (((X1) = (X0))
% 0.35/0.56          | ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.35/0.56              = (k2_tarski @ X1 @ X0)))),
% 0.35/0.56      inference('simplify', [status(thm)], ['9'])).
% 0.35/0.56  thf('11', plain,
% 0.35/0.56      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.35/0.56         != (k2_tarski @ sk_A @ sk_B))),
% 0.35/0.56      inference('demod', [status(thm)], ['0', '1'])).
% 0.35/0.56  thf('12', plain,
% 0.35/0.56      ((((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))
% 0.35/0.56        | ((sk_A) = (sk_B)))),
% 0.35/0.56      inference('sup-', [status(thm)], ['10', '11'])).
% 0.35/0.56  thf('13', plain, (((sk_A) = (sk_B))),
% 0.35/0.56      inference('simplify', [status(thm)], ['12'])).
% 0.35/0.56  thf(t69_enumset1, axiom,
% 0.35/0.56    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.35/0.56  thf('14', plain,
% 0.35/0.56      (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 0.35/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.35/0.56  thf('15', plain,
% 0.35/0.56      (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 0.35/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.35/0.56  thf('16', plain,
% 0.35/0.56      (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 0.35/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.35/0.56  thf(t12_zfmisc_1, axiom,
% 0.35/0.56    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.35/0.56  thf('17', plain,
% 0.35/0.56      (![X36 : $i, X37 : $i]:
% 0.35/0.56         (r1_tarski @ (k1_tarski @ X36) @ (k2_tarski @ X36 @ X37))),
% 0.35/0.56      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.35/0.56  thf('18', plain,
% 0.35/0.56      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.35/0.56      inference('sup+', [status(thm)], ['16', '17'])).
% 0.35/0.56  thf(l32_xboole_1, axiom,
% 0.35/0.56    (![A:$i,B:$i]:
% 0.35/0.56     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.35/0.56  thf('19', plain,
% 0.35/0.56      (![X2 : $i, X4 : $i]:
% 0.35/0.56         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.35/0.56      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.35/0.56  thf('20', plain,
% 0.35/0.56      (![X0 : $i]:
% 0.35/0.56         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.35/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.35/0.56  thf('21', plain,
% 0.35/0.56      (![X0 : $i]:
% 0.35/0.56         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X0))
% 0.35/0.56           = (k1_xboole_0))),
% 0.35/0.56      inference('sup+', [status(thm)], ['15', '20'])).
% 0.35/0.56  thf('22', plain,
% 0.35/0.56      (![X11 : $i, X12 : $i]:
% 0.35/0.56         ((k2_xboole_0 @ X11 @ X12)
% 0.35/0.56           = (k5_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11)))),
% 0.35/0.56      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.35/0.56  thf('23', plain,
% 0.35/0.56      (![X0 : $i]:
% 0.35/0.56         ((k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0))
% 0.35/0.56           = (k5_xboole_0 @ (k2_tarski @ X0 @ X0) @ k1_xboole_0))),
% 0.35/0.56      inference('sup+', [status(thm)], ['21', '22'])).
% 0.35/0.56  thf(t5_boole, axiom,
% 0.35/0.56    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.35/0.56  thf('24', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.35/0.56      inference('cnf', [status(esa)], [t5_boole])).
% 0.35/0.56  thf('25', plain,
% 0.35/0.56      (![X0 : $i]:
% 0.35/0.56         ((k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0))
% 0.35/0.56           = (k2_tarski @ X0 @ X0))),
% 0.35/0.56      inference('demod', [status(thm)], ['23', '24'])).
% 0.35/0.56  thf('26', plain,
% 0.35/0.56      (![X0 : $i]:
% 0.35/0.56         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.35/0.56           = (k2_tarski @ X0 @ X0))),
% 0.35/0.56      inference('sup+', [status(thm)], ['14', '25'])).
% 0.35/0.56  thf('27', plain,
% 0.35/0.56      (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 0.35/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.35/0.56  thf('28', plain, (((sk_A) = (sk_B))),
% 0.35/0.56      inference('simplify', [status(thm)], ['12'])).
% 0.35/0.56  thf('29', plain,
% 0.35/0.56      (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 0.35/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.35/0.56  thf('30', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 0.35/0.56      inference('demod', [status(thm)], ['2', '13', '26', '27', '28', '29'])).
% 0.35/0.56  thf('31', plain, ($false), inference('simplify', [status(thm)], ['30'])).
% 0.35/0.56  
% 0.35/0.56  % SZS output end Refutation
% 0.35/0.56  
% 0.35/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
