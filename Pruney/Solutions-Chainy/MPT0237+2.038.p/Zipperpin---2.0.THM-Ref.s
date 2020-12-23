%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9CeQ3T5Xga

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:03 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 105 expanded)
%              Number of leaves         :   25 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :  411 ( 847 expanded)
%              Number of equality atoms :   53 ( 106 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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
    ! [X31: $i,X32: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X31 @ X32 ) )
      = ( k2_xboole_0 @ X31 @ X32 ) ) ),
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
    ! [X37: $i,X38: $i] :
      ( ( ( k5_xboole_0 @ ( k1_tarski @ X37 ) @ ( k1_tarski @ X38 ) )
        = ( k2_tarski @ X37 @ X38 ) )
      | ( X37 = X38 ) ) ),
    inference(cnf,[status(esa)],[t29_zfmisc_1])).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('4',plain,(
    ! [X35: $i,X36: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X35 ) @ ( k1_tarski @ X36 ) )
      | ( X35 = X36 ) ) ),
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

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('10',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['6','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X1 = X0 )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['3','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('18',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['18'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('20',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X33: $i,X34: $i] :
      ( r1_tarski @ ( k1_tarski @ X33 ) @ ( k2_tarski @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('22',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k5_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('26',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','27'])).

thf('29',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('30',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['18'])).

thf('31',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('32',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['2','19','28','29','30','31'])).

thf('33',plain,(
    $false ),
    inference(simplify,[status(thm)],['32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9CeQ3T5Xga
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:49:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.58  % Solved by: fo/fo7.sh
% 0.37/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.58  % done 275 iterations in 0.132s
% 0.37/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.58  % SZS output start Refutation
% 0.37/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.58  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.37/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.58  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.58  thf(t32_zfmisc_1, conjecture,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 0.37/0.58       ( k2_tarski @ A @ B ) ))).
% 0.37/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.58    (~( ![A:$i,B:$i]:
% 0.37/0.58        ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 0.37/0.58          ( k2_tarski @ A @ B ) ) )),
% 0.37/0.58    inference('cnf.neg', [status(esa)], [t32_zfmisc_1])).
% 0.37/0.58  thf('0', plain,
% 0.37/0.58      (((k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 0.37/0.58         != (k2_tarski @ sk_A @ sk_B))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(l51_zfmisc_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.37/0.58  thf('1', plain,
% 0.37/0.58      (![X31 : $i, X32 : $i]:
% 0.37/0.58         ((k3_tarski @ (k2_tarski @ X31 @ X32)) = (k2_xboole_0 @ X31 @ X32))),
% 0.37/0.58      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.37/0.58  thf('2', plain,
% 0.37/0.58      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.37/0.58         != (k2_tarski @ sk_A @ sk_B))),
% 0.37/0.58      inference('demod', [status(thm)], ['0', '1'])).
% 0.37/0.58  thf(t29_zfmisc_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( ( A ) != ( B ) ) =>
% 0.37/0.58       ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.37/0.58         ( k2_tarski @ A @ B ) ) ))).
% 0.37/0.58  thf('3', plain,
% 0.37/0.58      (![X37 : $i, X38 : $i]:
% 0.37/0.58         (((k5_xboole_0 @ (k1_tarski @ X37) @ (k1_tarski @ X38))
% 0.37/0.58            = (k2_tarski @ X37 @ X38))
% 0.37/0.58          | ((X37) = (X38)))),
% 0.37/0.58      inference('cnf', [status(esa)], [t29_zfmisc_1])).
% 0.37/0.58  thf(t17_zfmisc_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( ( A ) != ( B ) ) =>
% 0.37/0.58       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.37/0.58  thf('4', plain,
% 0.37/0.58      (![X35 : $i, X36 : $i]:
% 0.37/0.58         ((r1_xboole_0 @ (k1_tarski @ X35) @ (k1_tarski @ X36))
% 0.37/0.58          | ((X35) = (X36)))),
% 0.37/0.58      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.37/0.58  thf(t83_xboole_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.37/0.58  thf('5', plain,
% 0.37/0.58      (![X8 : $i, X9 : $i]:
% 0.37/0.58         (((k4_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 0.37/0.58      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.37/0.58  thf('6', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (((X1) = (X0))
% 0.37/0.58          | ((k4_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.37/0.58              = (k1_tarski @ X1)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['4', '5'])).
% 0.37/0.58  thf(commutativity_k3_xboole_0, axiom,
% 0.37/0.58    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.37/0.58  thf('7', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.58  thf(t94_xboole_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( k2_xboole_0 @ A @ B ) =
% 0.37/0.58       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.58  thf('8', plain,
% 0.37/0.58      (![X14 : $i, X15 : $i]:
% 0.37/0.58         ((k2_xboole_0 @ X14 @ X15)
% 0.37/0.58           = (k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ 
% 0.37/0.58              (k3_xboole_0 @ X14 @ X15)))),
% 0.37/0.58      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.37/0.58  thf(t91_xboole_1, axiom,
% 0.37/0.58    (![A:$i,B:$i,C:$i]:
% 0.37/0.58     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.37/0.58       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.37/0.58  thf('9', plain,
% 0.37/0.58      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.37/0.58         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 0.37/0.58           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 0.37/0.58      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.37/0.58  thf('10', plain,
% 0.37/0.58      (![X14 : $i, X15 : $i]:
% 0.37/0.58         ((k2_xboole_0 @ X14 @ X15)
% 0.37/0.58           = (k5_xboole_0 @ X14 @ 
% 0.37/0.58              (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X14 @ X15))))),
% 0.37/0.58      inference('demod', [status(thm)], ['8', '9'])).
% 0.37/0.58  thf('11', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         ((k2_xboole_0 @ X0 @ X1)
% 0.37/0.58           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.37/0.58      inference('sup+', [status(thm)], ['7', '10'])).
% 0.37/0.58  thf(t100_xboole_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.58  thf('12', plain,
% 0.37/0.58      (![X5 : $i, X6 : $i]:
% 0.37/0.58         ((k4_xboole_0 @ X5 @ X6)
% 0.37/0.58           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.37/0.58      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.58  thf('13', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         ((k2_xboole_0 @ X0 @ X1)
% 0.37/0.58           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.37/0.58      inference('demod', [status(thm)], ['11', '12'])).
% 0.37/0.58  thf('14', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.37/0.58            = (k5_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))
% 0.37/0.58          | ((X0) = (X1)))),
% 0.37/0.58      inference('sup+', [status(thm)], ['6', '13'])).
% 0.37/0.58  thf('15', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.37/0.58            = (k2_tarski @ X1 @ X0))
% 0.37/0.58          | ((X1) = (X0))
% 0.37/0.58          | ((X0) = (X1)))),
% 0.37/0.58      inference('sup+', [status(thm)], ['3', '14'])).
% 0.37/0.58  thf('16', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (((X1) = (X0))
% 0.37/0.58          | ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.37/0.58              = (k2_tarski @ X1 @ X0)))),
% 0.37/0.58      inference('simplify', [status(thm)], ['15'])).
% 0.37/0.58  thf('17', plain,
% 0.37/0.58      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.37/0.58         != (k2_tarski @ sk_A @ sk_B))),
% 0.37/0.58      inference('demod', [status(thm)], ['0', '1'])).
% 0.37/0.58  thf('18', plain,
% 0.37/0.58      ((((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))
% 0.37/0.58        | ((sk_A) = (sk_B)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['16', '17'])).
% 0.37/0.58  thf('19', plain, (((sk_A) = (sk_B))),
% 0.37/0.58      inference('simplify', [status(thm)], ['18'])).
% 0.37/0.58  thf(t69_enumset1, axiom,
% 0.37/0.58    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.37/0.58  thf('20', plain,
% 0.37/0.58      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.37/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.58  thf(t12_zfmisc_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.37/0.58  thf('21', plain,
% 0.37/0.58      (![X33 : $i, X34 : $i]:
% 0.37/0.58         (r1_tarski @ (k1_tarski @ X33) @ (k2_tarski @ X33 @ X34))),
% 0.37/0.58      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.37/0.58  thf(l32_xboole_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.58  thf('22', plain,
% 0.37/0.58      (![X2 : $i, X4 : $i]:
% 0.37/0.58         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.37/0.58      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.37/0.58  thf('23', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         ((k4_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.37/0.58           = (k1_xboole_0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['21', '22'])).
% 0.37/0.58  thf('24', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         ((k2_xboole_0 @ X0 @ X1)
% 0.37/0.58           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.37/0.58      inference('demod', [status(thm)], ['11', '12'])).
% 0.37/0.58  thf('25', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 0.37/0.58           = (k5_xboole_0 @ (k2_tarski @ X1 @ X0) @ k1_xboole_0))),
% 0.37/0.58      inference('sup+', [status(thm)], ['23', '24'])).
% 0.37/0.58  thf(t5_boole, axiom,
% 0.37/0.58    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.58  thf('26', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.37/0.58      inference('cnf', [status(esa)], [t5_boole])).
% 0.37/0.58  thf('27', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 0.37/0.58           = (k2_tarski @ X1 @ X0))),
% 0.37/0.58      inference('demod', [status(thm)], ['25', '26'])).
% 0.37/0.58  thf('28', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.37/0.58           = (k2_tarski @ X0 @ X0))),
% 0.37/0.58      inference('sup+', [status(thm)], ['20', '27'])).
% 0.37/0.58  thf('29', plain,
% 0.37/0.58      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.37/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.58  thf('30', plain, (((sk_A) = (sk_B))),
% 0.37/0.58      inference('simplify', [status(thm)], ['18'])).
% 0.37/0.58  thf('31', plain,
% 0.37/0.58      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.37/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.58  thf('32', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 0.37/0.58      inference('demod', [status(thm)], ['2', '19', '28', '29', '30', '31'])).
% 0.37/0.58  thf('33', plain, ($false), inference('simplify', [status(thm)], ['32'])).
% 0.37/0.58  
% 0.37/0.58  % SZS output end Refutation
% 0.37/0.58  
% 0.37/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
