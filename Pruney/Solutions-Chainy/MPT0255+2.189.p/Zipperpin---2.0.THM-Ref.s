%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RhcftMRyJc

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   21 (  21 expanded)
%              Number of leaves         :   11 (  11 expanded)
%              Depth                    :    6
%              Number of atoms          :   89 (  89 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t50_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t50_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t15_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ A @ B )
        = k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k2_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_xboole_1])).

thf('2',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['2'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_tarski @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ X5 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    $false ),
    inference(simplify,[status(thm)],['7'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RhcftMRyJc
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:49:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 6 iterations in 0.008s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(t50_zfmisc_1, conjecture,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.46        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 0.21/0.46  thf('0', plain,
% 0.21/0.46      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t15_xboole_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( ( k2_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.46       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.46  thf('1', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         (((X0) = (k1_xboole_0)) | ((k2_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 0.21/0.46      inference('cnf', [status(esa)], [t15_xboole_1])).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.46        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.46  thf('3', plain, (((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.21/0.46      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.46  thf(t41_enumset1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( k2_tarski @ A @ B ) =
% 0.21/0.46       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.21/0.46  thf('4', plain,
% 0.21/0.46      (![X2 : $i, X3 : $i]:
% 0.21/0.46         ((k2_tarski @ X2 @ X3)
% 0.21/0.46           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k1_tarski @ X3)))),
% 0.21/0.46      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.21/0.46  thf(t49_zfmisc_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.21/0.46  thf('5', plain,
% 0.21/0.46      (![X4 : $i, X5 : $i]:
% 0.21/0.46         ((k2_xboole_0 @ (k1_tarski @ X4) @ X5) != (k1_xboole_0))),
% 0.21/0.46      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.21/0.46  thf('6', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) != (k1_xboole_0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.46  thf('7', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['3', '6'])).
% 0.21/0.46  thf('8', plain, ($false), inference('simplify', [status(thm)], ['7'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
