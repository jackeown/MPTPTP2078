%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.O28yW8wkLk

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:05 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   25 (  25 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    6
%              Number of atoms          :  113 ( 113 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t22_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t22_zfmisc_1])).

thf('0',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_A @ sk_B ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ ( k1_tarski @ X26 ) @ ( k2_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = X2 )
      | ~ ( r1_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_tarski @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('6',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ X4 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','7'])).

thf('9',plain,(
    $false ),
    inference(simplify,[status(thm)],['8'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.O28yW8wkLk
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:16:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 31 iterations in 0.016s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.46  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.19/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.46  thf(t22_zfmisc_1, conjecture,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.19/0.46       ( k1_xboole_0 ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i,B:$i]:
% 0.19/0.46        ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.19/0.46          ( k1_xboole_0 ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t22_zfmisc_1])).
% 0.19/0.46  thf('0', plain,
% 0.19/0.46      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_B))
% 0.19/0.46         != (k1_xboole_0))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(t12_zfmisc_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.19/0.46  thf('1', plain,
% 0.19/0.46      (![X26 : $i, X27 : $i]:
% 0.19/0.46         (r1_tarski @ (k1_tarski @ X26) @ (k2_tarski @ X26 @ X27))),
% 0.19/0.46      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.19/0.46  thf(t28_xboole_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.46  thf('2', plain,
% 0.19/0.46      (![X2 : $i, X3 : $i]:
% 0.19/0.46         (((k3_xboole_0 @ X2 @ X3) = (X2)) | ~ (r1_tarski @ X2 @ X3))),
% 0.19/0.46      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.46  thf('3', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         ((k3_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.19/0.46           = (k1_tarski @ X1))),
% 0.19/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.46  thf(t100_xboole_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.46  thf('4', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         ((k4_xboole_0 @ X0 @ X1)
% 0.19/0.46           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.19/0.46      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.19/0.46  thf('5', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))
% 0.19/0.46           = (k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 0.19/0.46      inference('sup+', [status(thm)], ['3', '4'])).
% 0.19/0.46  thf(t92_xboole_1, axiom,
% 0.19/0.46    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.19/0.46  thf('6', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ X4) = (k1_xboole_0))),
% 0.19/0.46      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.19/0.46  thf('7', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))
% 0.19/0.46           = (k1_xboole_0))),
% 0.19/0.46      inference('demod', [status(thm)], ['5', '6'])).
% 0.19/0.46  thf('8', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.19/0.46      inference('demod', [status(thm)], ['0', '7'])).
% 0.19/0.46  thf('9', plain, ($false), inference('simplify', [status(thm)], ['8'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
