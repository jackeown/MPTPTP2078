%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kReQ6XDoXl

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:12 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   23 (  26 expanded)
%              Number of leaves         :   10 (  12 expanded)
%              Depth                    :    7
%              Number of atoms          :  196 ( 239 expanded)
%              Number of equality atoms :   23 (  28 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('0',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X6 ) @ ( k1_tarski @ X7 ) )
        = ( k1_tarski @ X6 ) )
      | ( X6 = X7 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf(t42_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X4 ) @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X4 @ X3 ) ) ) ),
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

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('5',plain,(
    ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_B ) )
 != ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_C @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_C @ ( k1_tarski @ sk_B ) ) @ ( k1_tarski @ sk_A ) )
     != ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_C @ ( k1_tarski @ sk_B ) ) ) )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('8',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_C @ ( k1_tarski @ sk_B ) ) )
     != ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_C @ ( k1_tarski @ sk_B ) ) ) )
    | ( sk_A = sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.10  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kReQ6XDoXl
% 0.09/0.29  % Computer   : n014.cluster.edu
% 0.09/0.29  % Model      : x86_64 x86_64
% 0.09/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.29  % Memory     : 8042.1875MB
% 0.09/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.29  % CPULimit   : 60
% 0.09/0.29  % DateTime   : Tue Dec  1 15:19:07 EST 2020
% 0.09/0.29  % CPUTime    : 
% 0.09/0.29  % Running portfolio for 600 s
% 0.09/0.29  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.09/0.29  % Number of cores: 8
% 0.09/0.30  % Python version: Python 3.6.8
% 0.09/0.30  % Running in FO mode
% 0.14/0.36  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.14/0.36  % Solved by: fo/fo7.sh
% 0.14/0.36  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.14/0.36  % done 18 iterations in 0.008s
% 0.14/0.36  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.14/0.36  % SZS output start Refutation
% 0.14/0.36  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.14/0.36  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.14/0.36  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.14/0.36  thf(sk_A_type, type, sk_A: $i).
% 0.14/0.36  thf(sk_B_type, type, sk_B: $i).
% 0.14/0.36  thf(sk_C_type, type, sk_C: $i).
% 0.14/0.36  thf(t20_zfmisc_1, axiom,
% 0.14/0.36    (![A:$i,B:$i]:
% 0.14/0.36     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.14/0.36         ( k1_tarski @ A ) ) <=>
% 0.14/0.36       ( ( A ) != ( B ) ) ))).
% 0.14/0.36  thf('0', plain,
% 0.14/0.36      (![X6 : $i, X7 : $i]:
% 0.14/0.36         (((k4_xboole_0 @ (k1_tarski @ X6) @ (k1_tarski @ X7))
% 0.14/0.36            = (k1_tarski @ X6))
% 0.14/0.36          | ((X6) = (X7)))),
% 0.14/0.36      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.14/0.36  thf(t42_xboole_1, axiom,
% 0.14/0.36    (![A:$i,B:$i,C:$i]:
% 0.14/0.36     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.14/0.36       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.14/0.36  thf('1', plain,
% 0.14/0.36      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.14/0.36         ((k4_xboole_0 @ (k2_xboole_0 @ X2 @ X4) @ X3)
% 0.14/0.36           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X4 @ X3)))),
% 0.14/0.36      inference('cnf', [status(esa)], [t42_xboole_1])).
% 0.14/0.36  thf('2', plain,
% 0.14/0.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.14/0.36         (((k4_xboole_0 @ (k2_xboole_0 @ X2 @ (k1_tarski @ X0)) @ 
% 0.14/0.36            (k1_tarski @ X1))
% 0.14/0.36            = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k1_tarski @ X1)) @ 
% 0.14/0.36               (k1_tarski @ X0)))
% 0.14/0.36          | ((X0) = (X1)))),
% 0.14/0.36      inference('sup+', [status(thm)], ['0', '1'])).
% 0.14/0.36  thf(t147_zfmisc_1, conjecture,
% 0.14/0.36    (![A:$i,B:$i,C:$i]:
% 0.14/0.36     ( ( ( A ) != ( B ) ) =>
% 0.14/0.36       ( ( k4_xboole_0 @
% 0.14/0.36           ( k2_xboole_0 @ C @ ( k1_tarski @ A ) ) @ ( k1_tarski @ B ) ) =
% 0.14/0.36         ( k2_xboole_0 @
% 0.14/0.36           ( k4_xboole_0 @ C @ ( k1_tarski @ B ) ) @ ( k1_tarski @ A ) ) ) ))).
% 0.14/0.36  thf(zf_stmt_0, negated_conjecture,
% 0.14/0.36    (~( ![A:$i,B:$i,C:$i]:
% 0.14/0.36        ( ( ( A ) != ( B ) ) =>
% 0.14/0.36          ( ( k4_xboole_0 @
% 0.14/0.36              ( k2_xboole_0 @ C @ ( k1_tarski @ A ) ) @ ( k1_tarski @ B ) ) =
% 0.14/0.36            ( k2_xboole_0 @
% 0.14/0.36              ( k4_xboole_0 @ C @ ( k1_tarski @ B ) ) @ ( k1_tarski @ A ) ) ) ) )),
% 0.14/0.36    inference('cnf.neg', [status(esa)], [t147_zfmisc_1])).
% 0.14/0.36  thf('3', plain,
% 0.14/0.36      (((k4_xboole_0 @ (k2_xboole_0 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.14/0.36         (k1_tarski @ sk_B))
% 0.14/0.36         != (k2_xboole_0 @ (k4_xboole_0 @ sk_C @ (k1_tarski @ sk_B)) @ 
% 0.14/0.36             (k1_tarski @ sk_A)))),
% 0.14/0.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.14/0.36  thf(commutativity_k2_xboole_0, axiom,
% 0.14/0.36    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.14/0.36  thf('4', plain,
% 0.14/0.36      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.14/0.36      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.14/0.36  thf('5', plain,
% 0.14/0.36      (((k4_xboole_0 @ (k2_xboole_0 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.14/0.36         (k1_tarski @ sk_B))
% 0.14/0.36         != (k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.14/0.36             (k4_xboole_0 @ sk_C @ (k1_tarski @ sk_B))))),
% 0.14/0.36      inference('demod', [status(thm)], ['3', '4'])).
% 0.14/0.36  thf('6', plain,
% 0.14/0.36      ((((k2_xboole_0 @ (k4_xboole_0 @ sk_C @ (k1_tarski @ sk_B)) @ 
% 0.14/0.36          (k1_tarski @ sk_A))
% 0.14/0.36          != (k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.14/0.36              (k4_xboole_0 @ sk_C @ (k1_tarski @ sk_B))))
% 0.14/0.36        | ((sk_A) = (sk_B)))),
% 0.14/0.36      inference('sup-', [status(thm)], ['2', '5'])).
% 0.14/0.36  thf('7', plain,
% 0.14/0.36      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.14/0.36      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.14/0.36  thf('8', plain,
% 0.14/0.36      ((((k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.14/0.36          (k4_xboole_0 @ sk_C @ (k1_tarski @ sk_B)))
% 0.14/0.36          != (k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.14/0.36              (k4_xboole_0 @ sk_C @ (k1_tarski @ sk_B))))
% 0.14/0.36        | ((sk_A) = (sk_B)))),
% 0.14/0.36      inference('demod', [status(thm)], ['6', '7'])).
% 0.14/0.36  thf('9', plain, (((sk_A) = (sk_B))),
% 0.14/0.36      inference('simplify', [status(thm)], ['8'])).
% 0.14/0.36  thf('10', plain, (((sk_A) != (sk_B))),
% 0.14/0.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.14/0.36  thf('11', plain, ($false),
% 0.14/0.36      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.14/0.36  
% 0.14/0.36  % SZS output end Refutation
% 0.14/0.36  
% 0.14/0.37  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
