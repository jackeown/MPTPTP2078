%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RRzXIX07vt

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   38 (  46 expanded)
%              Number of leaves         :   17 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :  319 ( 399 expanded)
%              Number of equality atoms :   26 (  34 expanded)
%              Maximal formula depth    :   12 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t65_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) )
      = ( k1_tarski @ ( k4_mcart_1 @ A @ B @ C @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k4_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) )
        = ( k1_tarski @ ( k4_mcart_1 @ A @ B @ C @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_mcart_1])).

thf('0',plain,(
    ( k4_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) )
 != ( k1_tarski @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
      = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X2 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_zfmisc_1 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) @ X2 )
      = ( k2_zfmisc_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_zfmisc_1 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ ( k1_tarski @ X2 ) @ ( k1_tarski @ X1 ) @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k4_zfmisc_1 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X13 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ ( k1_tarski @ X2 ) @ ( k1_tarski @ X1 ) @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X2 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) @ X2 )
      = ( k2_zfmisc_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ X2 ) @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ ( k4_tarski @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_mcart_1 @ X3 @ X4 @ X5 )
      = ( k4_tarski @ ( k4_tarski @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ X2 ) @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_mcart_1 @ X3 @ X4 @ X5 )
      = ( k4_tarski @ ( k4_tarski @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('14',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_mcart_1 @ X3 @ X4 @ X5 )
      = ( k4_tarski @ ( k4_tarski @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_mcart_1 @ ( k4_tarski @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(d4_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ) )).

thf('16',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k4_mcart_1 @ X9 @ X10 @ X11 @ X12 )
      = ( k4_tarski @ ( k3_mcart_1 @ X9 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_mcart_1 @ ( k4_tarski @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_mcart_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ( k1_tarski @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
 != ( k1_tarski @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['0','7','12','17'])).

thf('19',plain,(
    $false ),
    inference(simplify,[status(thm)],['18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RRzXIX07vt
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:44:40 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 32 iterations in 0.028s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.20/0.48  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.48  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.48  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.48  thf(t65_mcart_1, conjecture,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( k4_zfmisc_1 @
% 0.20/0.48         ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) @ 
% 0.20/0.48         ( k1_tarski @ D ) ) =
% 0.20/0.48       ( k1_tarski @ ( k4_mcart_1 @ A @ B @ C @ D ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48        ( ( k4_zfmisc_1 @
% 0.20/0.48            ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) @ 
% 0.20/0.48            ( k1_tarski @ D ) ) =
% 0.20/0.48          ( k1_tarski @ ( k4_mcart_1 @ A @ B @ C @ D ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t65_mcart_1])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (((k4_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B) @ 
% 0.20/0.48         (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))
% 0.20/0.48         != (k1_tarski @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t35_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.48       ( k1_tarski @ ( k4_tarski @ A @ B ) ) ))).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X1 : $i, X2 : $i]:
% 0.20/0.48         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X2))
% 0.20/0.48           = (k1_tarski @ (k4_tarski @ X1 @ X2)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 0.20/0.48  thf(d3_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.20/0.48       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.48         ((k3_zfmisc_1 @ X6 @ X7 @ X8)
% 0.20/0.48           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X8))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         ((k3_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0) @ X2)
% 0.20/0.48           = (k2_zfmisc_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)) @ X2))),
% 0.20/0.48      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.48         ((k3_zfmisc_1 @ X6 @ X7 @ X8)
% 0.20/0.48           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X8))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         ((k3_zfmisc_1 @ (k1_tarski @ (k4_tarski @ X2 @ X1)) @ X0 @ X3)
% 0.20/0.48           = (k2_zfmisc_1 @ 
% 0.20/0.48              (k3_zfmisc_1 @ (k1_tarski @ X2) @ (k1_tarski @ X1) @ X0) @ X3))),
% 0.20/0.48      inference('sup+', [status(thm)], ['3', '4'])).
% 0.20/0.48  thf(d4_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.20/0.48       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.48         ((k4_zfmisc_1 @ X13 @ X14 @ X15 @ X16)
% 0.20/0.48           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X13 @ X14 @ X15) @ X16))),
% 0.20/0.48      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         ((k3_zfmisc_1 @ (k1_tarski @ (k4_tarski @ X2 @ X1)) @ X0 @ X3)
% 0.20/0.48           = (k4_zfmisc_1 @ (k1_tarski @ X2) @ (k1_tarski @ X1) @ X0 @ X3))),
% 0.20/0.48      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X1 : $i, X2 : $i]:
% 0.20/0.48         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X2))
% 0.20/0.48           = (k1_tarski @ (k4_tarski @ X1 @ X2)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         ((k3_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0) @ X2)
% 0.20/0.48           = (k2_zfmisc_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)) @ X2))),
% 0.20/0.48      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         ((k3_zfmisc_1 @ (k1_tarski @ X2) @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.20/0.48           = (k1_tarski @ (k4_tarski @ (k4_tarski @ X2 @ X1) @ X0)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['8', '9'])).
% 0.20/0.48  thf(d3_mcart_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.48         ((k3_mcart_1 @ X3 @ X4 @ X5)
% 0.20/0.48           = (k4_tarski @ (k4_tarski @ X3 @ X4) @ X5))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         ((k3_zfmisc_1 @ (k1_tarski @ X2) @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.20/0.48           = (k1_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0)))),
% 0.20/0.48      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.48         ((k3_mcart_1 @ X3 @ X4 @ X5)
% 0.20/0.48           = (k4_tarski @ (k4_tarski @ X3 @ X4) @ X5))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.48         ((k3_mcart_1 @ X3 @ X4 @ X5)
% 0.20/0.48           = (k4_tarski @ (k4_tarski @ X3 @ X4) @ X5))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         ((k3_mcart_1 @ (k4_tarski @ X2 @ X1) @ X0 @ X3)
% 0.20/0.48           = (k4_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0) @ X3))),
% 0.20/0.48      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.48  thf(d4_mcart_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 0.20/0.48       ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ))).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.48         ((k4_mcart_1 @ X9 @ X10 @ X11 @ X12)
% 0.20/0.48           = (k4_tarski @ (k3_mcart_1 @ X9 @ X10 @ X11) @ X12))),
% 0.20/0.48      inference('cnf', [status(esa)], [d4_mcart_1])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         ((k3_mcart_1 @ (k4_tarski @ X2 @ X1) @ X0 @ X3)
% 0.20/0.48           = (k4_mcart_1 @ X2 @ X1 @ X0 @ X3))),
% 0.20/0.48      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (((k1_tarski @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.20/0.48         != (k1_tarski @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 0.20/0.48      inference('demod', [status(thm)], ['0', '7', '12', '17'])).
% 0.20/0.48  thf('19', plain, ($false), inference('simplify', [status(thm)], ['18'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
