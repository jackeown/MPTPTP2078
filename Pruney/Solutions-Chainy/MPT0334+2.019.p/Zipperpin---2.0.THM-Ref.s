%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.k36w2rtIkP

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:12 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   18 (  20 expanded)
%              Number of leaves         :    9 (  10 expanded)
%              Depth                    :    5
%              Number of atoms          :  142 ( 178 expanded)
%              Number of equality atoms :   17 (  21 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('0',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X7 ) @ ( k1_tarski @ X8 ) )
        = ( k1_tarski @ X7 ) )
      | ( X7 = X8 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf(t42_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X1 ) )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k1_tarski @ X1 ) ) @ ( k1_tarski @ X0 ) ) )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t147_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( A != B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ C @ ( k1_tarski @ A ) ) @ ( k1_tarski @ B ) )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ C @ ( k1_tarski @ B ) ) @ ( k1_tarski @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( A != B )
       => ( ( k4_xboole_0 @ ( k2_xboole_0 @ C @ ( k1_tarski @ A ) ) @ ( k1_tarski @ B ) )
          = ( k2_xboole_0 @ ( k4_xboole_0 @ C @ ( k1_tarski @ B ) ) @ ( k1_tarski @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t147_zfmisc_1])).

thf('3',plain,(
    ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_B ) )
 != ( k2_xboole_0 @ ( k4_xboole_0 @ sk_C @ ( k1_tarski @ sk_B ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_B ) )
     != ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_B ) ) )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.k36w2rtIkP
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:53:29 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 29 iterations in 0.020s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.46  thf(t20_zfmisc_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.19/0.46         ( k1_tarski @ A ) ) <=>
% 0.19/0.46       ( ( A ) != ( B ) ) ))).
% 0.19/0.46  thf('0', plain,
% 0.19/0.46      (![X7 : $i, X8 : $i]:
% 0.19/0.46         (((k4_xboole_0 @ (k1_tarski @ X7) @ (k1_tarski @ X8))
% 0.19/0.46            = (k1_tarski @ X7))
% 0.19/0.46          | ((X7) = (X8)))),
% 0.19/0.46      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.19/0.46  thf(t42_xboole_1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.19/0.46       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.19/0.46  thf('1', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.46         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X2) @ X1)
% 0.19/0.46           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X2 @ X1)))),
% 0.19/0.46      inference('cnf', [status(esa)], [t42_xboole_1])).
% 0.19/0.46  thf('2', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.46         (((k4_xboole_0 @ (k2_xboole_0 @ X2 @ (k1_tarski @ X0)) @ 
% 0.19/0.46            (k1_tarski @ X1))
% 0.19/0.46            = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k1_tarski @ X1)) @ 
% 0.19/0.46               (k1_tarski @ X0)))
% 0.19/0.46          | ((X0) = (X1)))),
% 0.19/0.46      inference('sup+', [status(thm)], ['0', '1'])).
% 0.19/0.46  thf(t147_zfmisc_1, conjecture,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ( ( A ) != ( B ) ) =>
% 0.19/0.46       ( ( k4_xboole_0 @
% 0.19/0.46           ( k2_xboole_0 @ C @ ( k1_tarski @ A ) ) @ ( k1_tarski @ B ) ) =
% 0.19/0.46         ( k2_xboole_0 @
% 0.19/0.46           ( k4_xboole_0 @ C @ ( k1_tarski @ B ) ) @ ( k1_tarski @ A ) ) ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.46        ( ( ( A ) != ( B ) ) =>
% 0.19/0.46          ( ( k4_xboole_0 @
% 0.19/0.46              ( k2_xboole_0 @ C @ ( k1_tarski @ A ) ) @ ( k1_tarski @ B ) ) =
% 0.19/0.46            ( k2_xboole_0 @
% 0.19/0.46              ( k4_xboole_0 @ C @ ( k1_tarski @ B ) ) @ ( k1_tarski @ A ) ) ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t147_zfmisc_1])).
% 0.19/0.46  thf('3', plain,
% 0.19/0.46      (((k4_xboole_0 @ (k2_xboole_0 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.19/0.46         (k1_tarski @ sk_B))
% 0.19/0.46         != (k2_xboole_0 @ (k4_xboole_0 @ sk_C @ (k1_tarski @ sk_B)) @ 
% 0.19/0.46             (k1_tarski @ sk_A)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('4', plain,
% 0.19/0.46      ((((k4_xboole_0 @ (k2_xboole_0 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.19/0.46          (k1_tarski @ sk_B))
% 0.19/0.46          != (k4_xboole_0 @ (k2_xboole_0 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.19/0.46              (k1_tarski @ sk_B)))
% 0.19/0.46        | ((sk_A) = (sk_B)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.46  thf('5', plain, (((sk_A) = (sk_B))),
% 0.19/0.46      inference('simplify', [status(thm)], ['4'])).
% 0.19/0.46  thf('6', plain, (((sk_A) != (sk_B))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('7', plain, ($false),
% 0.19/0.46      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
