%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FqESjLGEyA

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   63 (  89 expanded)
%              Number of leaves         :   26 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :  411 ( 663 expanded)
%              Number of equality atoms :   57 (  91 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X48: $i,X49: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X48 @ X49 ) )
      = ( k2_xboole_0 @ X48 @ X49 ) ) ),
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
    ! [X52: $i,X53: $i] :
      ( ( ( k5_xboole_0 @ ( k1_tarski @ X52 ) @ ( k1_tarski @ X53 ) )
        = ( k2_tarski @ X52 @ X53 ) )
      | ( X52 = X53 ) ) ),
    inference(cnf,[status(esa)],[t29_zfmisc_1])).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('4',plain,(
    ! [X50: $i,X51: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X50 ) @ ( k1_tarski @ X51 ) )
      | ( X50 = X51 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_xboole_0 @ X11 @ X12 ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
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
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('15',plain,(
    ! [X44: $i,X46: $i,X47: $i] :
      ( ( r1_tarski @ X46 @ ( k2_tarski @ X44 @ X47 ) )
      | ( X46
       != ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('16',plain,(
    ! [X44: $i,X47: $i] :
      ( r1_tarski @ ( k1_tarski @ X44 ) @ ( k2_tarski @ X44 @ X47 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','16'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('22',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('23',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('26',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('29',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['21','30'])).

thf('32',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['12'])).

thf('33',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('34',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['2','13','31','32','33'])).

thf('35',plain,(
    $false ),
    inference(simplify,[status(thm)],['34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FqESjLGEyA
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:30:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 304 iterations in 0.106s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.55  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(t32_zfmisc_1, conjecture,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 0.21/0.55       ( k2_tarski @ A @ B ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i,B:$i]:
% 0.21/0.55        ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 0.21/0.55          ( k2_tarski @ A @ B ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t32_zfmisc_1])).
% 0.21/0.55  thf('0', plain,
% 0.21/0.55      (((k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 0.21/0.55         != (k2_tarski @ sk_A @ sk_B))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(l51_zfmisc_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.55  thf('1', plain,
% 0.21/0.55      (![X48 : $i, X49 : $i]:
% 0.21/0.55         ((k3_tarski @ (k2_tarski @ X48 @ X49)) = (k2_xboole_0 @ X48 @ X49))),
% 0.21/0.55      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.55         != (k2_tarski @ sk_A @ sk_B))),
% 0.21/0.55      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.55  thf(t29_zfmisc_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( A ) != ( B ) ) =>
% 0.21/0.55       ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.55         ( k2_tarski @ A @ B ) ) ))).
% 0.21/0.55  thf('3', plain,
% 0.21/0.55      (![X52 : $i, X53 : $i]:
% 0.21/0.55         (((k5_xboole_0 @ (k1_tarski @ X52) @ (k1_tarski @ X53))
% 0.21/0.55            = (k2_tarski @ X52 @ X53))
% 0.21/0.55          | ((X52) = (X53)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t29_zfmisc_1])).
% 0.21/0.55  thf(t17_zfmisc_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( A ) != ( B ) ) =>
% 0.21/0.55       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      (![X50 : $i, X51 : $i]:
% 0.21/0.55         ((r1_xboole_0 @ (k1_tarski @ X50) @ (k1_tarski @ X51))
% 0.21/0.55          | ((X50) = (X51)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.21/0.55  thf(t83_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (![X11 : $i, X12 : $i]:
% 0.21/0.55         (((k4_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_xboole_0 @ X11 @ X12))),
% 0.21/0.55      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.55  thf('6', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (((X1) = (X0))
% 0.21/0.55          | ((k4_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.21/0.55              = (k1_tarski @ X1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.55  thf(t98_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.21/0.55  thf('7', plain,
% 0.21/0.55      (![X14 : $i, X15 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ X14 @ X15)
% 0.21/0.55           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.21/0.55            = (k5_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))
% 0.21/0.55          | ((X0) = (X1)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.55  thf('9', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.21/0.55            = (k2_tarski @ X1 @ X0))
% 0.21/0.55          | ((X1) = (X0))
% 0.21/0.55          | ((X0) = (X1)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['3', '8'])).
% 0.21/0.55  thf('10', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (((X1) = (X0))
% 0.21/0.55          | ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.21/0.55              = (k2_tarski @ X1 @ X0)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.55         != (k2_tarski @ sk_A @ sk_B))),
% 0.21/0.55      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      ((((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))
% 0.21/0.55        | ((sk_A) = (sk_B)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.55  thf('13', plain, (((sk_A) = (sk_B))),
% 0.21/0.55      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.55  thf(t69_enumset1, axiom,
% 0.21/0.55    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.55  thf('14', plain,
% 0.21/0.55      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.21/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.55  thf(l45_zfmisc_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.21/0.55       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.21/0.55            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.21/0.55  thf('15', plain,
% 0.21/0.55      (![X44 : $i, X46 : $i, X47 : $i]:
% 0.21/0.56         ((r1_tarski @ X46 @ (k2_tarski @ X44 @ X47))
% 0.21/0.56          | ((X46) != (k1_tarski @ X44)))),
% 0.21/0.56      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.21/0.56  thf('16', plain,
% 0.21/0.56      (![X44 : $i, X47 : $i]:
% 0.21/0.56         (r1_tarski @ (k1_tarski @ X44) @ (k2_tarski @ X44 @ X47))),
% 0.21/0.56      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.56  thf('17', plain,
% 0.21/0.56      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.21/0.56      inference('sup+', [status(thm)], ['14', '16'])).
% 0.21/0.56  thf(l32_xboole_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.56  thf('18', plain,
% 0.21/0.56      (![X2 : $i, X4 : $i]:
% 0.21/0.56         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.21/0.56      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.56  thf('19', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.56  thf('20', plain,
% 0.21/0.56      (![X14 : $i, X15 : $i]:
% 0.21/0.56         ((k2_xboole_0 @ X14 @ X15)
% 0.21/0.56           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.21/0.56  thf('21', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.21/0.56           = (k5_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))),
% 0.21/0.56      inference('sup+', [status(thm)], ['19', '20'])).
% 0.21/0.56  thf(t17_xboole_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.56  thf('22', plain,
% 0.21/0.56      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 0.21/0.56      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.21/0.56  thf(t3_xboole_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.56  thf('23', plain,
% 0.21/0.56      (![X10 : $i]:
% 0.21/0.56         (((X10) = (k1_xboole_0)) | ~ (r1_tarski @ X10 @ k1_xboole_0))),
% 0.21/0.56      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.21/0.56  thf('24', plain,
% 0.21/0.56      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.56  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.56    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.56  thf('25', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.56  thf(t100_xboole_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.56  thf('26', plain,
% 0.21/0.56      (![X5 : $i, X6 : $i]:
% 0.21/0.56         ((k4_xboole_0 @ X5 @ X6)
% 0.21/0.56           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.56  thf('27', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((k4_xboole_0 @ X0 @ X1)
% 0.21/0.56           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['25', '26'])).
% 0.21/0.56  thf('28', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.56      inference('sup+', [status(thm)], ['24', '27'])).
% 0.21/0.56  thf(t3_boole, axiom,
% 0.21/0.56    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.56  thf('29', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.21/0.56      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.56  thf('30', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.56      inference('sup+', [status(thm)], ['28', '29'])).
% 0.21/0.56  thf('31', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.21/0.56           = (k1_tarski @ X0))),
% 0.21/0.56      inference('demod', [status(thm)], ['21', '30'])).
% 0.21/0.56  thf('32', plain, (((sk_A) = (sk_B))),
% 0.21/0.56      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.56  thf('33', plain,
% 0.21/0.56      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.21/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.56  thf('34', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['2', '13', '31', '32', '33'])).
% 0.21/0.56  thf('35', plain, ($false), inference('simplify', [status(thm)], ['34'])).
% 0.21/0.56  
% 0.21/0.56  % SZS output end Refutation
% 0.21/0.56  
% 0.21/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
