%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gczdimN87B

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:37 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   17 (  17 expanded)
%              Number of leaves         :   10 (  10 expanded)
%              Depth                    :    5
%              Number of atoms          :  107 ( 107 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   13 (   7 average)

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

thf(t53_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) @ D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k4_zfmisc_1 @ A @ B @ C @ D )
        = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) @ D ) ) ),
    inference('cnf.neg',[status(esa)],[t53_mcart_1])).

thf('0',plain,(
    ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_D ) ),
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
    ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('4',plain,(
    ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    $false ),
    inference(simplify,[status(thm)],['4'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gczdimN87B
% 0.15/0.38  % Computer   : n018.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 19:24:57 EST 2020
% 0.15/0.39  % CPUTime    : 
% 0.15/0.39  % Running portfolio for 600 s
% 0.15/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.39  % Number of cores: 8
% 0.15/0.39  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 0.24/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.50  % Solved by: fo/fo7.sh
% 0.24/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.50  % done 3 iterations in 0.008s
% 0.24/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.50  % SZS output start Refutation
% 0.24/0.50  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.24/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.24/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.50  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.24/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.24/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.24/0.50  thf(t53_mcart_1, conjecture,
% 0.24/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.50     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.24/0.50       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) @ D ) ))).
% 0.24/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.50    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.50        ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.24/0.50          ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) @ D ) ) )),
% 0.24/0.50    inference('cnf.neg', [status(esa)], [t53_mcart_1])).
% 0.24/0.50  thf('0', plain,
% 0.24/0.50      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.24/0.50         != (k2_zfmisc_1 @ 
% 0.24/0.50             (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C) @ sk_D))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf(d3_zfmisc_1, axiom,
% 0.24/0.50    (![A:$i,B:$i,C:$i]:
% 0.24/0.50     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.24/0.50       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.24/0.50  thf('1', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.50         ((k3_zfmisc_1 @ X0 @ X1 @ X2)
% 0.24/0.50           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1) @ X2))),
% 0.24/0.50      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.24/0.50  thf('2', plain,
% 0.24/0.50      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.24/0.50         != (k2_zfmisc_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) @ sk_D))),
% 0.24/0.50      inference('demod', [status(thm)], ['0', '1'])).
% 0.24/0.50  thf(d4_zfmisc_1, axiom,
% 0.24/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.50     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.24/0.50       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.24/0.50  thf('3', plain,
% 0.24/0.50      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.24/0.50         ((k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6)
% 0.24/0.50           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X4 @ X5) @ X6))),
% 0.24/0.50      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.24/0.50  thf('4', plain,
% 0.24/0.50      (((k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.24/0.50         != (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.24/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.24/0.50  thf('5', plain, ($false), inference('simplify', [status(thm)], ['4'])).
% 0.24/0.50  
% 0.24/0.50  % SZS output end Refutation
% 0.24/0.50  
% 0.24/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
