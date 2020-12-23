%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jd5rR2LgDq

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:54 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   41 (  51 expanded)
%              Number of leaves         :   17 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :  301 ( 386 expanded)
%              Number of equality atoms :   40 (  52 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t23_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X15 @ X16 ) @ ( k1_tarski @ X16 ) )
        = ( k1_tarski @ X15 ) )
      | ( X15 = X16 ) ) ),
    inference(cnf,[status(esa)],[t23_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X0 @ X0 ) )
        = ( k1_tarski @ X1 ) )
      | ( X1 = X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X8 @ X9 ) @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_tarski @ X0 @ X1 )
        = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k3_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k3_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X1 @ X1 ) ) ) ) )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['2','7'])).

thf('9',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X11 @ X10 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t19_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k1_tarski @ A ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X13 ) @ ( k2_tarski @ X13 @ X14 ) )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t19_zfmisc_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_tarski @ X0 @ X1 )
        = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) )
      | ( X0 = X1 ) ) ),
    inference(demod,[status(thm)],['8','15','16'])).

thf(t29_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k2_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( A != B )
       => ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k2_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_zfmisc_1])).

thf('18',plain,(
    ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['20','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jd5rR2LgDq
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:22:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.35/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.57  % Solved by: fo/fo7.sh
% 0.35/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.57  % done 223 iterations in 0.123s
% 0.35/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.57  % SZS output start Refutation
% 0.35/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.35/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.35/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.35/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.35/0.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.35/0.57  thf(t69_enumset1, axiom,
% 0.35/0.57    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.35/0.57  thf('0', plain, (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.35/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.35/0.57  thf(t23_zfmisc_1, axiom,
% 0.35/0.57    (![A:$i,B:$i]:
% 0.35/0.57     ( ( ( A ) != ( B ) ) =>
% 0.35/0.57       ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ B ) ) =
% 0.35/0.57         ( k1_tarski @ A ) ) ))).
% 0.35/0.57  thf('1', plain,
% 0.35/0.57      (![X15 : $i, X16 : $i]:
% 0.35/0.57         (((k4_xboole_0 @ (k2_tarski @ X15 @ X16) @ (k1_tarski @ X16))
% 0.35/0.57            = (k1_tarski @ X15))
% 0.35/0.57          | ((X15) = (X16)))),
% 0.35/0.57      inference('cnf', [status(esa)], [t23_zfmisc_1])).
% 0.35/0.57  thf('2', plain,
% 0.35/0.57      (![X0 : $i, X1 : $i]:
% 0.35/0.57         (((k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X0 @ X0))
% 0.35/0.57            = (k1_tarski @ X1))
% 0.35/0.57          | ((X1) = (X0)))),
% 0.35/0.57      inference('sup+', [status(thm)], ['0', '1'])).
% 0.35/0.57  thf(t100_xboole_1, axiom,
% 0.35/0.57    (![A:$i,B:$i]:
% 0.35/0.57     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.35/0.57  thf('3', plain,
% 0.35/0.57      (![X2 : $i, X3 : $i]:
% 0.35/0.57         ((k4_xboole_0 @ X2 @ X3)
% 0.35/0.57           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.35/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.35/0.57  thf(t94_xboole_1, axiom,
% 0.35/0.57    (![A:$i,B:$i]:
% 0.35/0.57     ( ( k2_xboole_0 @ A @ B ) =
% 0.35/0.57       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.35/0.57  thf('4', plain,
% 0.35/0.57      (![X8 : $i, X9 : $i]:
% 0.35/0.57         ((k2_xboole_0 @ X8 @ X9)
% 0.35/0.57           = (k5_xboole_0 @ (k5_xboole_0 @ X8 @ X9) @ (k3_xboole_0 @ X8 @ X9)))),
% 0.35/0.57      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.35/0.57  thf('5', plain,
% 0.35/0.57      (![X0 : $i, X1 : $i]:
% 0.35/0.57         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.35/0.57           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 0.35/0.57              (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.35/0.57      inference('sup+', [status(thm)], ['3', '4'])).
% 0.35/0.57  thf(t22_xboole_1, axiom,
% 0.35/0.57    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.35/0.57  thf('6', plain,
% 0.35/0.57      (![X4 : $i, X5 : $i]:
% 0.35/0.57         ((k2_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)) = (X4))),
% 0.35/0.57      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.35/0.57  thf('7', plain,
% 0.35/0.57      (![X0 : $i, X1 : $i]:
% 0.35/0.57         ((X1)
% 0.35/0.57           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 0.35/0.57              (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.35/0.57      inference('demod', [status(thm)], ['5', '6'])).
% 0.35/0.57  thf('8', plain,
% 0.35/0.57      (![X0 : $i, X1 : $i]:
% 0.35/0.57         (((k2_tarski @ X0 @ X1)
% 0.35/0.57            = (k5_xboole_0 @ (k1_tarski @ X0) @ 
% 0.35/0.57               (k3_xboole_0 @ (k2_tarski @ X0 @ X1) @ 
% 0.35/0.57                (k3_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X1)))))
% 0.35/0.57          | ((X0) = (X1)))),
% 0.35/0.57      inference('sup+', [status(thm)], ['2', '7'])).
% 0.35/0.57  thf('9', plain, (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.35/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.35/0.57  thf(commutativity_k2_tarski, axiom,
% 0.35/0.57    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.35/0.57  thf('10', plain,
% 0.35/0.57      (![X10 : $i, X11 : $i]:
% 0.35/0.57         ((k2_tarski @ X11 @ X10) = (k2_tarski @ X10 @ X11))),
% 0.35/0.57      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.35/0.57  thf(t19_zfmisc_1, axiom,
% 0.35/0.57    (![A:$i,B:$i]:
% 0.35/0.57     ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.35/0.57       ( k1_tarski @ A ) ))).
% 0.35/0.57  thf('11', plain,
% 0.35/0.57      (![X13 : $i, X14 : $i]:
% 0.35/0.57         ((k3_xboole_0 @ (k1_tarski @ X13) @ (k2_tarski @ X13 @ X14))
% 0.35/0.57           = (k1_tarski @ X13))),
% 0.35/0.57      inference('cnf', [status(esa)], [t19_zfmisc_1])).
% 0.35/0.57  thf(commutativity_k3_xboole_0, axiom,
% 0.35/0.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.35/0.57  thf('12', plain,
% 0.35/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.35/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.35/0.57  thf('13', plain,
% 0.35/0.57      (![X0 : $i, X1 : $i]:
% 0.35/0.57         ((k3_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k1_tarski @ X0))
% 0.35/0.57           = (k1_tarski @ X0))),
% 0.35/0.57      inference('sup+', [status(thm)], ['11', '12'])).
% 0.35/0.57  thf('14', plain,
% 0.35/0.57      (![X0 : $i, X1 : $i]:
% 0.35/0.57         ((k3_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0))
% 0.35/0.57           = (k1_tarski @ X0))),
% 0.35/0.57      inference('sup+', [status(thm)], ['10', '13'])).
% 0.35/0.57  thf('15', plain,
% 0.35/0.57      (![X0 : $i, X1 : $i]:
% 0.35/0.57         ((k3_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X0 @ X0))
% 0.35/0.57           = (k1_tarski @ X0))),
% 0.35/0.57      inference('sup+', [status(thm)], ['9', '14'])).
% 0.35/0.57  thf('16', plain,
% 0.35/0.57      (![X0 : $i, X1 : $i]:
% 0.35/0.57         ((k3_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0))
% 0.35/0.57           = (k1_tarski @ X0))),
% 0.35/0.57      inference('sup+', [status(thm)], ['10', '13'])).
% 0.35/0.57  thf('17', plain,
% 0.35/0.57      (![X0 : $i, X1 : $i]:
% 0.35/0.57         (((k2_tarski @ X0 @ X1)
% 0.35/0.57            = (k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))
% 0.35/0.57          | ((X0) = (X1)))),
% 0.35/0.57      inference('demod', [status(thm)], ['8', '15', '16'])).
% 0.35/0.57  thf(t29_zfmisc_1, conjecture,
% 0.35/0.57    (![A:$i,B:$i]:
% 0.35/0.57     ( ( ( A ) != ( B ) ) =>
% 0.35/0.57       ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.35/0.57         ( k2_tarski @ A @ B ) ) ))).
% 0.35/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.57    (~( ![A:$i,B:$i]:
% 0.35/0.57        ( ( ( A ) != ( B ) ) =>
% 0.35/0.57          ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.35/0.57            ( k2_tarski @ A @ B ) ) ) )),
% 0.35/0.57    inference('cnf.neg', [status(esa)], [t29_zfmisc_1])).
% 0.35/0.57  thf('18', plain,
% 0.35/0.57      (((k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.35/0.57         != (k2_tarski @ sk_A @ sk_B))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('19', plain,
% 0.35/0.57      ((((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))
% 0.35/0.57        | ((sk_A) = (sk_B)))),
% 0.35/0.57      inference('sup-', [status(thm)], ['17', '18'])).
% 0.35/0.57  thf('20', plain, (((sk_A) = (sk_B))),
% 0.35/0.57      inference('simplify', [status(thm)], ['19'])).
% 0.35/0.57  thf('21', plain, (((sk_A) != (sk_B))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('22', plain, ($false),
% 0.35/0.57      inference('simplify_reflect-', [status(thm)], ['20', '21'])).
% 0.35/0.57  
% 0.35/0.57  % SZS output end Refutation
% 0.35/0.57  
% 0.35/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
