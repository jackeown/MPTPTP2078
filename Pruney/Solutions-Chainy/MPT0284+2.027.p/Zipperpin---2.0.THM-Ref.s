%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.seduUuUeWW

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:50 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   16 (  16 expanded)
%              Number of leaves         :   10 (  10 expanded)
%              Depth                    :    3
%              Number of atoms          :   99 (  99 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t86_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) ) @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ B @ A ) ) ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) ) @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ B @ A ) ) ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t86_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf(t81_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ X2 ) @ ( k1_zfmisc_1 @ X3 ) ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t81_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    $false ),
    inference(demod,[status(thm)],['0','3'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.seduUuUeWW
% 0.13/0.33  % Computer   : n007.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:46:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 3 iterations in 0.007s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.46  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.19/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.46  thf(t86_zfmisc_1, conjecture,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( r1_tarski @
% 0.19/0.46       ( k2_xboole_0 @
% 0.19/0.46         ( k1_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) ) @ 
% 0.19/0.46         ( k1_zfmisc_1 @ ( k4_xboole_0 @ B @ A ) ) ) @ 
% 0.19/0.46       ( k1_zfmisc_1 @ ( k5_xboole_0 @ A @ B ) ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i,B:$i]:
% 0.19/0.46        ( r1_tarski @
% 0.19/0.46          ( k2_xboole_0 @
% 0.19/0.46            ( k1_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) ) @ 
% 0.19/0.46            ( k1_zfmisc_1 @ ( k4_xboole_0 @ B @ A ) ) ) @ 
% 0.19/0.46          ( k1_zfmisc_1 @ ( k5_xboole_0 @ A @ B ) ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t86_zfmisc_1])).
% 0.19/0.46  thf('0', plain,
% 0.19/0.46      (~ (r1_tarski @ 
% 0.19/0.46          (k2_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_B)) @ 
% 0.19/0.46           (k1_zfmisc_1 @ (k4_xboole_0 @ sk_B @ sk_A))) @ 
% 0.19/0.46          (k1_zfmisc_1 @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(d6_xboole_0, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( k5_xboole_0 @ A @ B ) =
% 0.19/0.46       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.19/0.46  thf('1', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         ((k5_xboole_0 @ X0 @ X1)
% 0.19/0.46           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.19/0.46      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.19/0.46  thf(t81_zfmisc_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( r1_tarski @
% 0.19/0.46       ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) @ 
% 0.19/0.46       ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.19/0.46  thf('2', plain,
% 0.19/0.46      (![X2 : $i, X3 : $i]:
% 0.19/0.46         (r1_tarski @ 
% 0.19/0.46          (k2_xboole_0 @ (k1_zfmisc_1 @ X2) @ (k1_zfmisc_1 @ X3)) @ 
% 0.19/0.46          (k1_zfmisc_1 @ (k2_xboole_0 @ X2 @ X3)))),
% 0.19/0.46      inference('cnf', [status(esa)], [t81_zfmisc_1])).
% 0.19/0.46  thf('3', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         (r1_tarski @ 
% 0.19/0.46          (k2_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 0.19/0.46           (k1_zfmisc_1 @ (k4_xboole_0 @ X0 @ X1))) @ 
% 0.19/0.46          (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.19/0.46      inference('sup+', [status(thm)], ['1', '2'])).
% 0.19/0.46  thf('4', plain, ($false), inference('demod', [status(thm)], ['0', '3'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
