%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rV114Ev9QG

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   19 (  20 expanded)
%              Number of leaves         :   10 (  11 expanded)
%              Depth                    :    5
%              Number of atoms          :  127 ( 137 expanded)
%              Number of equality atoms :   11 (  12 expanded)
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

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    $false ),
    inference(simplify,[status(thm)],['6'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rV114Ev9QG
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:06:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.47  % Solved by: fo/fo7.sh
% 0.22/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.47  % done 4 iterations in 0.009s
% 0.22/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.47  % SZS output start Refutation
% 0.22/0.47  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.22/0.47  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.47  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.22/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.47  thf(t54_mcart_1, conjecture,
% 0.22/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.47     ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C @ D ) =
% 0.22/0.47       ( k4_zfmisc_1 @ A @ B @ C @ D ) ))).
% 0.22/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.47    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.47        ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C @ D ) =
% 0.22/0.47          ( k4_zfmisc_1 @ A @ B @ C @ D ) ) )),
% 0.22/0.47    inference('cnf.neg', [status(esa)], [t54_mcart_1])).
% 0.22/0.47  thf('0', plain,
% 0.22/0.47      (((k3_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C @ sk_D)
% 0.22/0.47         != (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf(d3_zfmisc_1, axiom,
% 0.22/0.47    (![A:$i,B:$i,C:$i]:
% 0.22/0.47     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.22/0.47       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.22/0.47  thf('1', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.47         ((k3_zfmisc_1 @ X0 @ X1 @ X2)
% 0.22/0.47           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1) @ X2))),
% 0.22/0.47      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.22/0.47  thf('2', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.47         ((k3_zfmisc_1 @ X0 @ X1 @ X2)
% 0.22/0.47           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1) @ X2))),
% 0.22/0.47      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.22/0.47  thf('3', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.47         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.22/0.47           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 0.22/0.47      inference('sup+', [status(thm)], ['1', '2'])).
% 0.22/0.47  thf(d4_zfmisc_1, axiom,
% 0.22/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.47     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.22/0.47       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.22/0.47  thf('4', plain,
% 0.22/0.47      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.47         ((k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6)
% 0.22/0.47           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X4 @ X5) @ X6))),
% 0.22/0.47      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.22/0.47  thf('5', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.47         ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.22/0.47           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0))),
% 0.22/0.47      inference('sup+', [status(thm)], ['3', '4'])).
% 0.22/0.47  thf('6', plain,
% 0.22/0.47      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.22/0.47         != (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.22/0.47      inference('demod', [status(thm)], ['0', '5'])).
% 0.22/0.47  thf('7', plain, ($false), inference('simplify', [status(thm)], ['6'])).
% 0.22/0.47  
% 0.22/0.47  % SZS output end Refutation
% 0.22/0.47  
% 0.22/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
