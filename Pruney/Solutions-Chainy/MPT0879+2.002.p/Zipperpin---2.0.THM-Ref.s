%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ndLKBQRELI

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:22 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   21 (  22 expanded)
%              Number of leaves         :   12 (  13 expanded)
%              Depth                    :    4
%              Number of atoms          :  134 ( 144 expanded)
%              Number of equality atoms :   12 (  13 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t39_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) )
      = ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k3_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) )
        = ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_mcart_1])).

thf('0',plain,(
    ( k3_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_C ) )
 != ( k1_tarski @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
      = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_zfmisc_1 @ X5 @ X6 @ X7 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) @ X2 )
      = ( k2_zfmisc_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k3_mcart_1 @ X2 @ X3 @ X4 )
      = ( k4_tarski @ ( k4_tarski @ X2 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('6',plain,(
    ( k1_tarski @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) )
 != ( k1_tarski @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','3','4','5'])).

thf('7',plain,(
    $false ),
    inference(simplify,[status(thm)],['6'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ndLKBQRELI
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:40:56 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.35  % Running portfolio for 600 s
% 0.21/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.21/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.22/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.45  % Solved by: fo/fo7.sh
% 0.22/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.45  % done 4 iterations in 0.006s
% 0.22/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.45  % SZS output start Refutation
% 0.22/0.45  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.22/0.45  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.45  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.45  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.45  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.22/0.45  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.45  thf(t39_mcart_1, conjecture,
% 0.22/0.45    (![A:$i,B:$i,C:$i]:
% 0.22/0.45     ( ( k3_zfmisc_1 @
% 0.22/0.45         ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) ) =
% 0.22/0.45       ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ))).
% 0.22/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.45    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.45        ( ( k3_zfmisc_1 @
% 0.22/0.45            ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) ) =
% 0.22/0.45          ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) )),
% 0.22/0.45    inference('cnf.neg', [status(esa)], [t39_mcart_1])).
% 0.22/0.45  thf('0', plain,
% 0.22/0.45      (((k3_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B) @ 
% 0.22/0.45         (k1_tarski @ sk_C)) != (k1_tarski @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C)))),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf(t35_zfmisc_1, axiom,
% 0.22/0.45    (![A:$i,B:$i]:
% 0.22/0.45     ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.22/0.45       ( k1_tarski @ ( k4_tarski @ A @ B ) ) ))).
% 0.22/0.45  thf('1', plain,
% 0.22/0.45      (![X0 : $i, X1 : $i]:
% 0.22/0.45         ((k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.22/0.45           = (k1_tarski @ (k4_tarski @ X0 @ X1)))),
% 0.22/0.45      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 0.22/0.45  thf(d3_zfmisc_1, axiom,
% 0.22/0.45    (![A:$i,B:$i,C:$i]:
% 0.22/0.45     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.22/0.45       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.22/0.45  thf('2', plain,
% 0.22/0.45      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.45         ((k3_zfmisc_1 @ X5 @ X6 @ X7)
% 0.22/0.45           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6) @ X7))),
% 0.22/0.45      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.22/0.45  thf('3', plain,
% 0.22/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.45         ((k3_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0) @ X2)
% 0.22/0.45           = (k2_zfmisc_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)) @ X2))),
% 0.22/0.45      inference('sup+', [status(thm)], ['1', '2'])).
% 0.22/0.45  thf('4', plain,
% 0.22/0.45      (![X0 : $i, X1 : $i]:
% 0.22/0.45         ((k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.22/0.45           = (k1_tarski @ (k4_tarski @ X0 @ X1)))),
% 0.22/0.45      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 0.22/0.45  thf(d3_mcart_1, axiom,
% 0.22/0.45    (![A:$i,B:$i,C:$i]:
% 0.22/0.45     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.22/0.45  thf('5', plain,
% 0.22/0.45      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.45         ((k3_mcart_1 @ X2 @ X3 @ X4)
% 0.22/0.45           = (k4_tarski @ (k4_tarski @ X2 @ X3) @ X4))),
% 0.22/0.45      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.22/0.45  thf('6', plain,
% 0.22/0.45      (((k1_tarski @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C))
% 0.22/0.45         != (k1_tarski @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C)))),
% 0.22/0.45      inference('demod', [status(thm)], ['0', '3', '4', '5'])).
% 0.22/0.45  thf('7', plain, ($false), inference('simplify', [status(thm)], ['6'])).
% 0.22/0.45  
% 0.22/0.45  % SZS output end Refutation
% 0.22/0.45  
% 0.22/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
