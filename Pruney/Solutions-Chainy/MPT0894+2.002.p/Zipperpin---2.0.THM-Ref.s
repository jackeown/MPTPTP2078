%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uSIji8nDCb

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:38 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   21 (  23 expanded)
%              Number of leaves         :   10 (  12 expanded)
%              Depth                    :    5
%              Number of atoms          :  151 ( 171 expanded)
%              Number of equality atoms :   13 (  15 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t54_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C @ D )
      = ( k4_zfmisc_1 @ A @ B @ C @ D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C @ D )
        = ( k4_zfmisc_1 @ A @ B @ C @ D ) ) ),
    inference('cnf.neg',[status(esa)],[t54_mcart_1])).

thf('0',plain,(
    ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C @ sk_D )
 != ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t53_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) @ D ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t53_mcart_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('6',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X4 @ X5 ) @ X6 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('8',plain,(
    ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('9',plain,(
    $false ),
    inference(simplify,[status(thm)],['8'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uSIji8nDCb
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:19:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 4 iterations in 0.010s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.19/0.46  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.46  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.19/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.46  thf(t54_mcart_1, conjecture,
% 0.19/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.46     ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C @ D ) =
% 0.19/0.46       ( k4_zfmisc_1 @ A @ B @ C @ D ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.46        ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C @ D ) =
% 0.19/0.46          ( k4_zfmisc_1 @ A @ B @ C @ D ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t54_mcart_1])).
% 0.19/0.46  thf('0', plain,
% 0.19/0.46      (((k3_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C @ sk_D)
% 0.19/0.46         != (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(d3_zfmisc_1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.19/0.46       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.19/0.46  thf('1', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.46         ((k3_zfmisc_1 @ X0 @ X1 @ X2)
% 0.19/0.46           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1) @ X2))),
% 0.19/0.46      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.19/0.46  thf('2', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.46         ((k3_zfmisc_1 @ X0 @ X1 @ X2)
% 0.19/0.46           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1) @ X2))),
% 0.19/0.46      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.19/0.46  thf('3', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.46         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.19/0.46           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 0.19/0.46      inference('sup+', [status(thm)], ['1', '2'])).
% 0.19/0.46  thf(t53_mcart_1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.46     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.19/0.46       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) @ D ) ))).
% 0.19/0.46  thf('4', plain,
% 0.19/0.46      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.46         ((k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6)
% 0.19/0.46           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5) @ X6))),
% 0.19/0.46      inference('cnf', [status(esa)], [t53_mcart_1])).
% 0.19/0.46  thf('5', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.46         ((k3_zfmisc_1 @ X0 @ X1 @ X2)
% 0.19/0.46           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1) @ X2))),
% 0.19/0.46      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.19/0.46  thf('6', plain,
% 0.19/0.46      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.46         ((k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6)
% 0.19/0.46           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X4 @ X5) @ X6))),
% 0.19/0.46      inference('demod', [status(thm)], ['4', '5'])).
% 0.19/0.46  thf('7', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.46         ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.19/0.46           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0))),
% 0.19/0.46      inference('sup+', [status(thm)], ['3', '6'])).
% 0.19/0.46  thf('8', plain,
% 0.19/0.46      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.19/0.46         != (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.19/0.46      inference('demod', [status(thm)], ['0', '7'])).
% 0.19/0.46  thf('9', plain, ($false), inference('simplify', [status(thm)], ['8'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
