%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mE0v7hEZ5x

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   58 (  93 expanded)
%              Number of leaves         :   23 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :  413 ( 724 expanded)
%              Number of equality atoms :   52 (  94 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

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
    ! [X35: $i,X36: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X35 @ X36 ) )
      = ( k2_xboole_0 @ X35 @ X36 ) ) ),
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
    ! [X39: $i,X40: $i] :
      ( ( ( k5_xboole_0 @ ( k1_tarski @ X39 ) @ ( k1_tarski @ X40 ) )
        = ( k2_tarski @ X39 @ X40 ) )
      | ( X39 = X40 ) ) ),
    inference(cnf,[status(esa)],[t29_zfmisc_1])).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('4',plain,(
    ! [X37: $i,X38: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X37 ) @ ( k1_tarski @ X38 ) )
      | ( X37 = X38 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('10',plain,
    ( ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( sk_A = sk_B )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf('12',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['11'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('13',plain,(
    ! [X14: $i] :
      ( ( k2_tarski @ X14 @ X14 )
      = ( k1_tarski @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('14',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X35 @ X36 ) )
      = ( k2_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['11'])).

thf('17',plain,(
    ! [X14: $i] :
      ( ( k2_tarski @ X14 @ X14 )
      = ( k1_tarski @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('18',plain,(
    ( k3_tarski @ ( k1_tarski @ ( k1_tarski @ sk_A ) ) )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['2','12','15','16','17'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('19',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k3_enumset1 @ X20 @ X20 @ X21 @ X22 @ X23 )
      = ( k2_enumset1 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_enumset1 @ X15 @ X15 @ X16 )
      = ( k2_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('21',plain,(
    ! [X14: $i] :
      ( ( k2_tarski @ X14 @ X14 )
      = ( k1_tarski @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('23',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k2_enumset1 @ X17 @ X17 @ X18 @ X19 )
      = ( k1_enumset1 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t47_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ) )).

thf('24',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k3_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X9 ) @ ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X1 @ X0 @ X0 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','26'])).

thf('28',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k2_enumset1 @ X17 @ X17 @ X18 @ X19 )
      = ( k1_enumset1 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k3_tarski @ ( k1_tarski @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('32',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['18','30','31'])).

thf('33',plain,(
    $false ),
    inference(simplify,[status(thm)],['32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mE0v7hEZ5x
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:29:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 57 iterations in 0.032s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.49  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.21/0.49  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.49  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.49  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.49  thf(t32_zfmisc_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 0.21/0.49       ( k2_tarski @ A @ B ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i]:
% 0.21/0.49        ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 0.21/0.49          ( k2_tarski @ A @ B ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t32_zfmisc_1])).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (((k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 0.21/0.49         != (k2_tarski @ sk_A @ sk_B))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(l51_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X35 : $i, X36 : $i]:
% 0.21/0.49         ((k3_tarski @ (k2_tarski @ X35 @ X36)) = (k2_xboole_0 @ X35 @ X36))),
% 0.21/0.49      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.49         != (k2_tarski @ sk_A @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf(t29_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( A ) != ( B ) ) =>
% 0.21/0.49       ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.49         ( k2_tarski @ A @ B ) ) ))).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X39 : $i, X40 : $i]:
% 0.21/0.49         (((k5_xboole_0 @ (k1_tarski @ X39) @ (k1_tarski @ X40))
% 0.21/0.49            = (k2_tarski @ X39 @ X40))
% 0.21/0.49          | ((X39) = (X40)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t29_zfmisc_1])).
% 0.21/0.49  thf(t17_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( A ) != ( B ) ) =>
% 0.21/0.49       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X37 : $i, X38 : $i]:
% 0.21/0.49         ((r1_xboole_0 @ (k1_tarski @ X37) @ (k1_tarski @ X38))
% 0.21/0.49          | ((X37) = (X38)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.21/0.49  thf(t83_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i]:
% 0.21/0.49         (((k4_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (((X1) = (X0))
% 0.21/0.49          | ((k4_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.21/0.49              = (k1_tarski @ X1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.49  thf(t98_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i]:
% 0.21/0.49         ((k2_xboole_0 @ X7 @ X8)
% 0.21/0.49           = (k5_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.21/0.49            = (k5_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))
% 0.21/0.49          | ((X0) = (X1)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.49         != (k2_tarski @ sk_A @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      ((((k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.49          != (k2_tarski @ sk_A @ sk_B))
% 0.21/0.49        | ((sk_B) = (sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      ((((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))
% 0.21/0.49        | ((sk_A) = (sk_B))
% 0.21/0.49        | ((sk_B) = (sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['3', '10'])).
% 0.21/0.49  thf('12', plain, (((sk_A) = (sk_B))),
% 0.21/0.49      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.49  thf(t69_enumset1, axiom,
% 0.21/0.49    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X14 : $i]: ((k2_tarski @ X14 @ X14) = (k1_tarski @ X14))),
% 0.21/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X35 : $i, X36 : $i]:
% 0.21/0.49         ((k3_tarski @ (k2_tarski @ X35 @ X36)) = (k2_xboole_0 @ X35 @ X36))),
% 0.21/0.49      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['13', '14'])).
% 0.21/0.49  thf('16', plain, (((sk_A) = (sk_B))),
% 0.21/0.49      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (![X14 : $i]: ((k2_tarski @ X14 @ X14) = (k1_tarski @ X14))),
% 0.21/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (((k3_tarski @ (k1_tarski @ (k1_tarski @ sk_A))) != (k1_tarski @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['2', '12', '15', '16', '17'])).
% 0.21/0.49  thf(t72_enumset1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.49         ((k3_enumset1 @ X20 @ X20 @ X21 @ X22 @ X23)
% 0.21/0.49           = (k2_enumset1 @ X20 @ X21 @ X22 @ X23))),
% 0.21/0.49      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.21/0.49  thf(t70_enumset1, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (![X15 : $i, X16 : $i]:
% 0.21/0.49         ((k1_enumset1 @ X15 @ X15 @ X16) = (k2_tarski @ X15 @ X16))),
% 0.21/0.49      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (![X14 : $i]: ((k2_tarski @ X14 @ X14) = (k1_tarski @ X14))),
% 0.21/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['20', '21'])).
% 0.21/0.49  thf(t71_enumset1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.49         ((k2_enumset1 @ X17 @ X17 @ X18 @ X19)
% 0.21/0.49           = (k1_enumset1 @ X17 @ X18 @ X19))),
% 0.21/0.49      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.21/0.49  thf(t47_enumset1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.49     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.21/0.49       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ))).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.49         ((k3_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13)
% 0.21/0.49           = (k2_xboole_0 @ (k1_tarski @ X9) @ 
% 0.21/0.49              (k2_enumset1 @ X10 @ X11 @ X12 @ X13)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         ((k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0)
% 0.21/0.49           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['23', '24'])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((k3_enumset1 @ X1 @ X0 @ X0 @ X0 @ X0)
% 0.21/0.49           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['22', '25'])).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((k2_enumset1 @ X0 @ X0 @ X0 @ X0)
% 0.21/0.49           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['19', '26'])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.49         ((k2_enumset1 @ X17 @ X17 @ X18 @ X19)
% 0.21/0.49           = (k1_enumset1 @ X17 @ X18 @ X19))),
% 0.21/0.49      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['13', '14'])).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((k1_enumset1 @ X0 @ X0 @ X0)
% 0.21/0.49           = (k3_tarski @ (k1_tarski @ (k1_tarski @ X0))))),
% 0.21/0.49      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['20', '21'])).
% 0.21/0.49  thf('32', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['18', '30', '31'])).
% 0.21/0.49  thf('33', plain, ($false), inference('simplify', [status(thm)], ['32'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
