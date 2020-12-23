%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aUsM3Pdx4h

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:01 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   61 (  94 expanded)
%              Number of leaves         :   25 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :  371 ( 663 expanded)
%              Number of equality atoms :   54 (  93 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ! [X44: $i,X45: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X44 @ X45 ) )
      = ( k2_xboole_0 @ X44 @ X45 ) ) ),
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
    ! [X48: $i,X49: $i] :
      ( ( ( k5_xboole_0 @ ( k1_tarski @ X48 ) @ ( k1_tarski @ X49 ) )
        = ( k2_tarski @ X48 @ X49 ) )
      | ( X48 = X49 ) ) ),
    inference(cnf,[status(esa)],[t29_zfmisc_1])).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('4',plain,(
    ! [X46: $i,X47: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X46 ) @ ( k1_tarski @ X47 ) )
      | ( X46 = X47 ) ) ),
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

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('15',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('16',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('21',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['12'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('32',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('33',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['2','13','30','31','32'])).

thf('34',plain,(
    $false ),
    inference(simplify,[status(thm)],['33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aUsM3Pdx4h
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:12:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.59  % Solved by: fo/fo7.sh
% 0.19/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.59  % done 406 iterations in 0.144s
% 0.19/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.59  % SZS output start Refutation
% 0.19/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.59  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.19/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.59  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.19/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.59  thf(t32_zfmisc_1, conjecture,
% 0.19/0.59    (![A:$i,B:$i]:
% 0.19/0.59     ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 0.19/0.59       ( k2_tarski @ A @ B ) ))).
% 0.19/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.59    (~( ![A:$i,B:$i]:
% 0.19/0.59        ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 0.19/0.59          ( k2_tarski @ A @ B ) ) )),
% 0.19/0.59    inference('cnf.neg', [status(esa)], [t32_zfmisc_1])).
% 0.19/0.59  thf('0', plain,
% 0.19/0.59      (((k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 0.19/0.59         != (k2_tarski @ sk_A @ sk_B))),
% 0.19/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.59  thf(l51_zfmisc_1, axiom,
% 0.19/0.59    (![A:$i,B:$i]:
% 0.19/0.59     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.19/0.59  thf('1', plain,
% 0.19/0.59      (![X44 : $i, X45 : $i]:
% 0.19/0.59         ((k3_tarski @ (k2_tarski @ X44 @ X45)) = (k2_xboole_0 @ X44 @ X45))),
% 0.19/0.59      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.19/0.59  thf('2', plain,
% 0.19/0.59      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.59         != (k2_tarski @ sk_A @ sk_B))),
% 0.19/0.59      inference('demod', [status(thm)], ['0', '1'])).
% 0.19/0.59  thf(t29_zfmisc_1, axiom,
% 0.19/0.59    (![A:$i,B:$i]:
% 0.19/0.59     ( ( ( A ) != ( B ) ) =>
% 0.19/0.59       ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.19/0.59         ( k2_tarski @ A @ B ) ) ))).
% 0.19/0.59  thf('3', plain,
% 0.19/0.59      (![X48 : $i, X49 : $i]:
% 0.19/0.59         (((k5_xboole_0 @ (k1_tarski @ X48) @ (k1_tarski @ X49))
% 0.19/0.59            = (k2_tarski @ X48 @ X49))
% 0.19/0.59          | ((X48) = (X49)))),
% 0.19/0.59      inference('cnf', [status(esa)], [t29_zfmisc_1])).
% 0.19/0.59  thf(t17_zfmisc_1, axiom,
% 0.19/0.59    (![A:$i,B:$i]:
% 0.19/0.59     ( ( ( A ) != ( B ) ) =>
% 0.19/0.59       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.19/0.59  thf('4', plain,
% 0.19/0.59      (![X46 : $i, X47 : $i]:
% 0.19/0.59         ((r1_xboole_0 @ (k1_tarski @ X46) @ (k1_tarski @ X47))
% 0.19/0.59          | ((X46) = (X47)))),
% 0.19/0.59      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.19/0.59  thf(t83_xboole_1, axiom,
% 0.19/0.59    (![A:$i,B:$i]:
% 0.19/0.59     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.59  thf('5', plain,
% 0.19/0.59      (![X11 : $i, X12 : $i]:
% 0.19/0.59         (((k4_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_xboole_0 @ X11 @ X12))),
% 0.19/0.59      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.19/0.59  thf('6', plain,
% 0.19/0.59      (![X0 : $i, X1 : $i]:
% 0.19/0.59         (((X1) = (X0))
% 0.19/0.59          | ((k4_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.19/0.59              = (k1_tarski @ X1)))),
% 0.19/0.59      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.59  thf(t98_xboole_1, axiom,
% 0.19/0.59    (![A:$i,B:$i]:
% 0.19/0.59     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.19/0.59  thf('7', plain,
% 0.19/0.59      (![X14 : $i, X15 : $i]:
% 0.19/0.59         ((k2_xboole_0 @ X14 @ X15)
% 0.19/0.59           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.19/0.59      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.19/0.59  thf('8', plain,
% 0.19/0.59      (![X0 : $i, X1 : $i]:
% 0.19/0.59         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.19/0.59            = (k5_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))
% 0.19/0.59          | ((X0) = (X1)))),
% 0.19/0.59      inference('sup+', [status(thm)], ['6', '7'])).
% 0.19/0.59  thf('9', plain,
% 0.19/0.59      (![X0 : $i, X1 : $i]:
% 0.19/0.59         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.19/0.59            = (k2_tarski @ X1 @ X0))
% 0.19/0.59          | ((X1) = (X0))
% 0.19/0.59          | ((X0) = (X1)))),
% 0.19/0.59      inference('sup+', [status(thm)], ['3', '8'])).
% 0.19/0.59  thf('10', plain,
% 0.19/0.59      (![X0 : $i, X1 : $i]:
% 0.19/0.59         (((X1) = (X0))
% 0.19/0.59          | ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.19/0.59              = (k2_tarski @ X1 @ X0)))),
% 0.19/0.59      inference('simplify', [status(thm)], ['9'])).
% 0.19/0.59  thf('11', plain,
% 0.19/0.59      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.59         != (k2_tarski @ sk_A @ sk_B))),
% 0.19/0.59      inference('demod', [status(thm)], ['0', '1'])).
% 0.19/0.59  thf('12', plain,
% 0.19/0.59      ((((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))
% 0.19/0.59        | ((sk_A) = (sk_B)))),
% 0.19/0.59      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.59  thf('13', plain, (((sk_A) = (sk_B))),
% 0.19/0.59      inference('simplify', [status(thm)], ['12'])).
% 0.19/0.59  thf(commutativity_k3_xboole_0, axiom,
% 0.19/0.59    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.19/0.59  thf('14', plain,
% 0.19/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.59  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.19/0.59  thf('15', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.19/0.59      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.59  thf(t28_xboole_1, axiom,
% 0.19/0.59    (![A:$i,B:$i]:
% 0.19/0.59     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.59  thf('16', plain,
% 0.19/0.59      (![X5 : $i, X6 : $i]:
% 0.19/0.59         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.19/0.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.59  thf('17', plain,
% 0.19/0.59      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.19/0.59      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.59  thf('18', plain,
% 0.19/0.59      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.59      inference('sup+', [status(thm)], ['14', '17'])).
% 0.19/0.59  thf(t100_xboole_1, axiom,
% 0.19/0.59    (![A:$i,B:$i]:
% 0.19/0.59     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.59  thf('19', plain,
% 0.19/0.59      (![X3 : $i, X4 : $i]:
% 0.19/0.59         ((k4_xboole_0 @ X3 @ X4)
% 0.19/0.59           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.19/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.19/0.59  thf('20', plain,
% 0.19/0.59      (![X0 : $i]:
% 0.19/0.59         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.19/0.59      inference('sup+', [status(thm)], ['18', '19'])).
% 0.19/0.59  thf(t5_boole, axiom,
% 0.19/0.59    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.19/0.59  thf('21', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.19/0.59      inference('cnf', [status(esa)], [t5_boole])).
% 0.19/0.59  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.19/0.59      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.59  thf(t48_xboole_1, axiom,
% 0.19/0.59    (![A:$i,B:$i]:
% 0.19/0.59     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.19/0.59  thf('23', plain,
% 0.19/0.59      (![X8 : $i, X9 : $i]:
% 0.19/0.59         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.19/0.59           = (k3_xboole_0 @ X8 @ X9))),
% 0.19/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.19/0.59  thf('24', plain,
% 0.19/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.19/0.59      inference('sup+', [status(thm)], ['22', '23'])).
% 0.19/0.59  thf('25', plain,
% 0.19/0.59      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.59      inference('sup+', [status(thm)], ['14', '17'])).
% 0.19/0.59  thf('26', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.19/0.59      inference('demod', [status(thm)], ['24', '25'])).
% 0.19/0.59  thf('27', plain,
% 0.19/0.59      (![X14 : $i, X15 : $i]:
% 0.19/0.59         ((k2_xboole_0 @ X14 @ X15)
% 0.19/0.59           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.19/0.59      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.19/0.59  thf('28', plain,
% 0.19/0.59      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.19/0.59      inference('sup+', [status(thm)], ['26', '27'])).
% 0.19/0.59  thf('29', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.19/0.59      inference('cnf', [status(esa)], [t5_boole])).
% 0.19/0.59  thf('30', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.19/0.59      inference('demod', [status(thm)], ['28', '29'])).
% 0.19/0.59  thf('31', plain, (((sk_A) = (sk_B))),
% 0.19/0.59      inference('simplify', [status(thm)], ['12'])).
% 0.19/0.59  thf(t69_enumset1, axiom,
% 0.19/0.59    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.59  thf('32', plain,
% 0.19/0.59      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.19/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.59  thf('33', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 0.19/0.59      inference('demod', [status(thm)], ['2', '13', '30', '31', '32'])).
% 0.19/0.59  thf('34', plain, ($false), inference('simplify', [status(thm)], ['33'])).
% 0.19/0.59  
% 0.19/0.59  % SZS output end Refutation
% 0.19/0.59  
% 0.43/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
