%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.p931Vvi3wA

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:00 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   55 (  98 expanded)
%              Number of leaves         :   23 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :  378 ( 788 expanded)
%              Number of equality atoms :   51 ( 102 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

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
    ! [X55: $i,X56: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X55 @ X56 ) )
      = ( k2_xboole_0 @ X55 @ X56 ) ) ),
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
    ! [X63: $i,X64: $i] :
      ( ( ( k5_xboole_0 @ ( k1_tarski @ X63 ) @ ( k1_tarski @ X64 ) )
        = ( k2_tarski @ X63 @ X64 ) )
      | ( X63 = X64 ) ) ),
    inference(cnf,[status(esa)],[t29_zfmisc_1])).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('4',plain,(
    ! [X57: $i,X58: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X57 ) @ ( k1_tarski @ X58 ) )
      | ( X57 = X58 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k5_xboole_0 @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['7','8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['6','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X1 = X0 )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['3','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('17',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['17'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('19',plain,(
    ! [X25: $i] :
      ( ( k2_tarski @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = k1_xboole_0 ) )).

thf('20',plain,(
    ! [X61: $i,X62: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X61 ) @ ( k2_tarski @ X61 @ X62 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t22_zfmisc_1])).

thf('21',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['7','8','11'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k5_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('23',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X25: $i] :
      ( ( k2_tarski @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('27',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['17'])).

thf('28',plain,(
    ! [X25: $i] :
      ( ( k2_tarski @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('29',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['2','18','25','26','27','28'])).

thf('30',plain,(
    $false ),
    inference(simplify,[status(thm)],['29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.p931Vvi3wA
% 0.13/0.36  % Computer   : n012.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 11:17:22 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.42/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.62  % Solved by: fo/fo7.sh
% 0.42/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.62  % done 476 iterations in 0.181s
% 0.42/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.62  % SZS output start Refutation
% 0.42/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.42/0.62  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.42/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.42/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.42/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.42/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.42/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.62  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.42/0.62  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.42/0.62  thf(t32_zfmisc_1, conjecture,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 0.42/0.62       ( k2_tarski @ A @ B ) ))).
% 0.42/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.62    (~( ![A:$i,B:$i]:
% 0.42/0.62        ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 0.42/0.62          ( k2_tarski @ A @ B ) ) )),
% 0.42/0.62    inference('cnf.neg', [status(esa)], [t32_zfmisc_1])).
% 0.42/0.62  thf('0', plain,
% 0.42/0.62      (((k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 0.42/0.62         != (k2_tarski @ sk_A @ sk_B))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(l51_zfmisc_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.42/0.62  thf('1', plain,
% 0.42/0.62      (![X55 : $i, X56 : $i]:
% 0.42/0.62         ((k3_tarski @ (k2_tarski @ X55 @ X56)) = (k2_xboole_0 @ X55 @ X56))),
% 0.42/0.62      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.42/0.62  thf('2', plain,
% 0.42/0.62      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.42/0.62         != (k2_tarski @ sk_A @ sk_B))),
% 0.42/0.62      inference('demod', [status(thm)], ['0', '1'])).
% 0.42/0.62  thf(t29_zfmisc_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( ( A ) != ( B ) ) =>
% 0.42/0.62       ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.42/0.62         ( k2_tarski @ A @ B ) ) ))).
% 0.42/0.62  thf('3', plain,
% 0.42/0.62      (![X63 : $i, X64 : $i]:
% 0.42/0.62         (((k5_xboole_0 @ (k1_tarski @ X63) @ (k1_tarski @ X64))
% 0.42/0.62            = (k2_tarski @ X63 @ X64))
% 0.42/0.62          | ((X63) = (X64)))),
% 0.42/0.62      inference('cnf', [status(esa)], [t29_zfmisc_1])).
% 0.42/0.62  thf(t17_zfmisc_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( ( A ) != ( B ) ) =>
% 0.42/0.62       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.42/0.62  thf('4', plain,
% 0.42/0.62      (![X57 : $i, X58 : $i]:
% 0.42/0.62         ((r1_xboole_0 @ (k1_tarski @ X57) @ (k1_tarski @ X58))
% 0.42/0.62          | ((X57) = (X58)))),
% 0.42/0.62      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.42/0.62  thf(t83_xboole_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.42/0.62  thf('5', plain,
% 0.42/0.62      (![X5 : $i, X6 : $i]:
% 0.42/0.62         (((k4_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_xboole_0 @ X5 @ X6))),
% 0.42/0.62      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.42/0.62  thf('6', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (((X1) = (X0))
% 0.42/0.62          | ((k4_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.42/0.62              = (k1_tarski @ X1)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['4', '5'])).
% 0.42/0.62  thf(t94_xboole_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( k2_xboole_0 @ A @ B ) =
% 0.42/0.62       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.42/0.62  thf('7', plain,
% 0.42/0.62      (![X11 : $i, X12 : $i]:
% 0.42/0.62         ((k2_xboole_0 @ X11 @ X12)
% 0.42/0.62           = (k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ 
% 0.42/0.62              (k3_xboole_0 @ X11 @ X12)))),
% 0.42/0.62      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.42/0.62  thf(t91_xboole_1, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i]:
% 0.42/0.62     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.42/0.62       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.42/0.62  thf('8', plain,
% 0.42/0.62      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.42/0.62         ((k5_xboole_0 @ (k5_xboole_0 @ X8 @ X9) @ X10)
% 0.42/0.62           = (k5_xboole_0 @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 0.42/0.62      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.42/0.62  thf(commutativity_k3_xboole_0, axiom,
% 0.42/0.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.42/0.62  thf('9', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.42/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.42/0.62  thf(t100_xboole_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.42/0.62  thf('10', plain,
% 0.42/0.62      (![X2 : $i, X3 : $i]:
% 0.42/0.62         ((k4_xboole_0 @ X2 @ X3)
% 0.42/0.62           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.42/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.42/0.62  thf('11', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         ((k4_xboole_0 @ X0 @ X1)
% 0.42/0.62           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.42/0.62      inference('sup+', [status(thm)], ['9', '10'])).
% 0.42/0.62  thf('12', plain,
% 0.42/0.62      (![X11 : $i, X12 : $i]:
% 0.42/0.62         ((k2_xboole_0 @ X11 @ X12)
% 0.42/0.62           = (k5_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11)))),
% 0.42/0.62      inference('demod', [status(thm)], ['7', '8', '11'])).
% 0.42/0.62  thf('13', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.42/0.62            = (k5_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))
% 0.42/0.62          | ((X0) = (X1)))),
% 0.42/0.62      inference('sup+', [status(thm)], ['6', '12'])).
% 0.42/0.62  thf('14', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.42/0.62            = (k2_tarski @ X1 @ X0))
% 0.42/0.62          | ((X1) = (X0))
% 0.42/0.62          | ((X0) = (X1)))),
% 0.42/0.62      inference('sup+', [status(thm)], ['3', '13'])).
% 0.42/0.62  thf('15', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (((X1) = (X0))
% 0.42/0.62          | ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.42/0.62              = (k2_tarski @ X1 @ X0)))),
% 0.42/0.62      inference('simplify', [status(thm)], ['14'])).
% 0.42/0.62  thf('16', plain,
% 0.42/0.62      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.42/0.62         != (k2_tarski @ sk_A @ sk_B))),
% 0.42/0.62      inference('demod', [status(thm)], ['0', '1'])).
% 0.42/0.62  thf('17', plain,
% 0.42/0.62      ((((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))
% 0.42/0.62        | ((sk_A) = (sk_B)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['15', '16'])).
% 0.42/0.62  thf('18', plain, (((sk_A) = (sk_B))),
% 0.42/0.62      inference('simplify', [status(thm)], ['17'])).
% 0.42/0.62  thf(t69_enumset1, axiom,
% 0.42/0.62    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.42/0.62  thf('19', plain,
% 0.42/0.62      (![X25 : $i]: ((k2_tarski @ X25 @ X25) = (k1_tarski @ X25))),
% 0.42/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.42/0.62  thf(t22_zfmisc_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.42/0.62       ( k1_xboole_0 ) ))).
% 0.42/0.62  thf('20', plain,
% 0.42/0.62      (![X61 : $i, X62 : $i]:
% 0.42/0.62         ((k4_xboole_0 @ (k1_tarski @ X61) @ (k2_tarski @ X61 @ X62))
% 0.42/0.62           = (k1_xboole_0))),
% 0.42/0.62      inference('cnf', [status(esa)], [t22_zfmisc_1])).
% 0.42/0.62  thf('21', plain,
% 0.42/0.62      (![X11 : $i, X12 : $i]:
% 0.42/0.62         ((k2_xboole_0 @ X11 @ X12)
% 0.42/0.62           = (k5_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11)))),
% 0.42/0.62      inference('demod', [status(thm)], ['7', '8', '11'])).
% 0.42/0.62  thf('22', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 0.42/0.62           = (k5_xboole_0 @ (k2_tarski @ X1 @ X0) @ k1_xboole_0))),
% 0.42/0.62      inference('sup+', [status(thm)], ['20', '21'])).
% 0.42/0.62  thf(t5_boole, axiom,
% 0.42/0.62    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.42/0.62  thf('23', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.42/0.62      inference('cnf', [status(esa)], [t5_boole])).
% 0.42/0.62  thf('24', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 0.42/0.62           = (k2_tarski @ X1 @ X0))),
% 0.42/0.62      inference('demod', [status(thm)], ['22', '23'])).
% 0.42/0.62  thf('25', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.42/0.62           = (k2_tarski @ X0 @ X0))),
% 0.42/0.62      inference('sup+', [status(thm)], ['19', '24'])).
% 0.42/0.62  thf('26', plain,
% 0.42/0.62      (![X25 : $i]: ((k2_tarski @ X25 @ X25) = (k1_tarski @ X25))),
% 0.42/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.42/0.62  thf('27', plain, (((sk_A) = (sk_B))),
% 0.42/0.62      inference('simplify', [status(thm)], ['17'])).
% 0.42/0.62  thf('28', plain,
% 0.42/0.62      (![X25 : $i]: ((k2_tarski @ X25 @ X25) = (k1_tarski @ X25))),
% 0.42/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.42/0.62  thf('29', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 0.42/0.62      inference('demod', [status(thm)], ['2', '18', '25', '26', '27', '28'])).
% 0.42/0.62  thf('30', plain, ($false), inference('simplify', [status(thm)], ['29'])).
% 0.42/0.62  
% 0.42/0.62  % SZS output end Refutation
% 0.42/0.62  
% 0.42/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
