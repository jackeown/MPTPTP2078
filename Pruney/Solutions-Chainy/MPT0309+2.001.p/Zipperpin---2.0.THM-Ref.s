%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tdUTLw4RFy

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:12 EST 2020

% Result     : Theorem 0.16s
% Output     : Refutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   23 (  28 expanded)
%              Number of leaves         :    9 (  14 expanded)
%              Depth                    :    6
%              Number of atoms          :  266 ( 351 expanded)
%              Number of equality atoms :   17 (  24 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t121_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ C @ D ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ A @ D ) ) @ ( k2_zfmisc_1 @ B @ C ) ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ C @ D ) )
        = ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ A @ D ) ) @ ( k2_zfmisc_1 @ B @ C ) ) @ ( k2_zfmisc_1 @ B @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t121_zfmisc_1])).

thf('0',plain,(
    ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ sk_C @ sk_D ) )
 != ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('4',plain,(
    ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ sk_C @ sk_D ) )
 != ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ) ) ) ),
    inference(demod,[status(thm)],['0','1','2','3'])).

thf(t120_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ ( k2_xboole_0 @ X3 @ X5 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X6 @ X3 ) @ ( k2_zfmisc_1 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('6',plain,(
    ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ sk_C @ sk_D ) )
 != ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) @ ( k2_zfmisc_1 @ sk_B @ ( k2_xboole_0 @ sk_C @ sk_D ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ ( k2_xboole_0 @ X3 @ X5 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X6 @ X3 ) @ ( k2_zfmisc_1 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_zfmisc_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ ( k2_zfmisc_1 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('11',plain,(
    ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ sk_C @ sk_D ) )
 != ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['6','9','10'])).

thf('12',plain,(
    $false ),
    inference(simplify,[status(thm)],['11'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tdUTLw4RFy
% 0.10/0.30  % Computer   : n018.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % DateTime   : Tue Dec  1 14:57:57 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.10/0.30  % Running portfolio for 600 s
% 0.10/0.30  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.10/0.30  % Number of cores: 8
% 0.10/0.30  % Python version: Python 3.6.8
% 0.10/0.30  % Running in FO mode
% 0.16/0.42  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.16/0.42  % Solved by: fo/fo7.sh
% 0.16/0.42  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.16/0.42  % done 9 iterations in 0.020s
% 0.16/0.42  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.16/0.42  % SZS output start Refutation
% 0.16/0.42  thf(sk_A_type, type, sk_A: $i).
% 0.16/0.42  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.16/0.42  thf(sk_D_type, type, sk_D: $i).
% 0.16/0.42  thf(sk_B_type, type, sk_B: $i).
% 0.16/0.42  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.16/0.42  thf(sk_C_type, type, sk_C: $i).
% 0.16/0.42  thf(t121_zfmisc_1, conjecture,
% 0.16/0.42    (![A:$i,B:$i,C:$i,D:$i]:
% 0.16/0.42     ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ C @ D ) ) =
% 0.16/0.42       ( k2_xboole_0 @
% 0.16/0.42         ( k2_xboole_0 @
% 0.16/0.42           ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ A @ D ) ) @ 
% 0.16/0.42           ( k2_zfmisc_1 @ B @ C ) ) @ 
% 0.16/0.42         ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.16/0.42  thf(zf_stmt_0, negated_conjecture,
% 0.16/0.42    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.16/0.42        ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ C @ D ) ) =
% 0.16/0.42          ( k2_xboole_0 @
% 0.16/0.42            ( k2_xboole_0 @
% 0.16/0.42              ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ A @ D ) ) @ 
% 0.16/0.42              ( k2_zfmisc_1 @ B @ C ) ) @ 
% 0.16/0.42            ( k2_zfmisc_1 @ B @ D ) ) ) )),
% 0.16/0.42    inference('cnf.neg', [status(esa)], [t121_zfmisc_1])).
% 0.16/0.42  thf('0', plain,
% 0.16/0.42      (((k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 0.16/0.42         (k2_xboole_0 @ sk_C @ sk_D))
% 0.16/0.42         != (k2_xboole_0 @ 
% 0.16/0.42             (k2_xboole_0 @ 
% 0.16/0.42              (k2_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_C) @ 
% 0.16/0.42               (k2_zfmisc_1 @ sk_A @ sk_D)) @ 
% 0.16/0.42              (k2_zfmisc_1 @ sk_B @ sk_C)) @ 
% 0.16/0.42             (k2_zfmisc_1 @ sk_B @ sk_D)))),
% 0.16/0.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.42  thf(t4_xboole_1, axiom,
% 0.16/0.42    (![A:$i,B:$i,C:$i]:
% 0.16/0.42     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.16/0.42       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.16/0.42  thf('1', plain,
% 0.16/0.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.16/0.42         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.16/0.42           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.16/0.42      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.16/0.42  thf('2', plain,
% 0.16/0.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.16/0.42         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.16/0.42           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.16/0.42      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.16/0.42  thf('3', plain,
% 0.16/0.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.16/0.42         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.16/0.42           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.16/0.42      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.16/0.42  thf('4', plain,
% 0.16/0.42      (((k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 0.16/0.42         (k2_xboole_0 @ sk_C @ sk_D))
% 0.16/0.42         != (k2_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_C) @ 
% 0.16/0.42             (k2_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_D) @ 
% 0.16/0.42              (k2_xboole_0 @ (k2_zfmisc_1 @ sk_B @ sk_C) @ 
% 0.16/0.42               (k2_zfmisc_1 @ sk_B @ sk_D)))))),
% 0.16/0.42      inference('demod', [status(thm)], ['0', '1', '2', '3'])).
% 0.16/0.42  thf(t120_zfmisc_1, axiom,
% 0.16/0.42    (![A:$i,B:$i,C:$i]:
% 0.16/0.42     ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.16/0.42         ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.16/0.42       ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.16/0.43         ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.16/0.43  thf('5', plain,
% 0.16/0.43      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.16/0.43         ((k2_zfmisc_1 @ X6 @ (k2_xboole_0 @ X3 @ X5))
% 0.16/0.43           = (k2_xboole_0 @ (k2_zfmisc_1 @ X6 @ X3) @ (k2_zfmisc_1 @ X6 @ X5)))),
% 0.16/0.43      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 0.16/0.43  thf('6', plain,
% 0.16/0.43      (((k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 0.16/0.43         (k2_xboole_0 @ sk_C @ sk_D))
% 0.16/0.43         != (k2_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_C) @ 
% 0.16/0.43             (k2_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_D) @ 
% 0.16/0.43              (k2_zfmisc_1 @ sk_B @ (k2_xboole_0 @ sk_C @ sk_D)))))),
% 0.16/0.43      inference('demod', [status(thm)], ['4', '5'])).
% 0.16/0.43  thf('7', plain,
% 0.16/0.43      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.16/0.43         ((k2_zfmisc_1 @ X6 @ (k2_xboole_0 @ X3 @ X5))
% 0.16/0.43           = (k2_xboole_0 @ (k2_zfmisc_1 @ X6 @ X3) @ (k2_zfmisc_1 @ X6 @ X5)))),
% 0.16/0.43      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 0.16/0.43  thf('8', plain,
% 0.16/0.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.16/0.43         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.16/0.43           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.16/0.43      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.16/0.43  thf('9', plain,
% 0.16/0.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.16/0.43         ((k2_xboole_0 @ (k2_zfmisc_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3)
% 0.16/0.43           = (k2_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1) @ 
% 0.16/0.43              (k2_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ X3)))),
% 0.16/0.43      inference('sup+', [status(thm)], ['7', '8'])).
% 0.16/0.43  thf('10', plain,
% 0.16/0.43      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.16/0.43         ((k2_zfmisc_1 @ (k2_xboole_0 @ X3 @ X5) @ X4)
% 0.16/0.43           = (k2_xboole_0 @ (k2_zfmisc_1 @ X3 @ X4) @ (k2_zfmisc_1 @ X5 @ X4)))),
% 0.16/0.43      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 0.16/0.43  thf('11', plain,
% 0.16/0.43      (((k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 0.16/0.43         (k2_xboole_0 @ sk_C @ sk_D))
% 0.16/0.43         != (k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 0.16/0.43             (k2_xboole_0 @ sk_C @ sk_D)))),
% 0.16/0.43      inference('demod', [status(thm)], ['6', '9', '10'])).
% 0.16/0.43  thf('12', plain, ($false), inference('simplify', [status(thm)], ['11'])).
% 0.16/0.43  
% 0.16/0.43  % SZS output end Refutation
% 0.16/0.43  
% 0.16/0.43  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
