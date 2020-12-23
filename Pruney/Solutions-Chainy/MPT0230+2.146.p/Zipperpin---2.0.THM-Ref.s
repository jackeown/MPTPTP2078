%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pSu6RBNytn

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   36 (  40 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :  199 ( 247 expanded)
%              Number of equality atoms :   35 (  43 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t25_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        & ( A != B )
        & ( A != C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
          & ( A != B )
          & ( A != C ) ) ),
    inference('cnf.neg',[status(esa)],[t25_zfmisc_1])).

thf('0',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t136_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != B )
        & ( A != C )
        & ( ( k4_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ A ) )
         != ( k2_tarski @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( X7 = X6 )
      | ( ( k4_xboole_0 @ ( k1_enumset1 @ X7 @ X6 @ X8 ) @ ( k1_tarski @ X7 ) )
        = ( k2_tarski @ X6 @ X8 ) )
      | ( X7 = X8 ) ) ),
    inference(cnf,[status(esa)],[t136_enumset1])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ ( k4_xboole_0 @ X4 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      | ( X2 = X0 )
      | ( X2 = X1 )
      | ( ( k1_tarski @ X2 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = sk_B )
    | ( sk_A = sk_C ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['4','5','6'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('8',plain,(
    ! [X30: $i,X31: $i] :
      ( ( X31 != X30 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X31 ) @ ( k1_tarski @ X30 ) )
       != ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('9',plain,(
    ! [X30: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X30 ) @ ( k1_tarski @ X30 ) )
     != ( k1_tarski @ X30 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('13',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('14',plain,(
    ! [X30: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X30 ) ) ),
    inference(demod,[status(thm)],['9','12','13'])).

thf('15',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,(
    $false ),
    inference(simplify,[status(thm)],['15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pSu6RBNytn
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 14:17:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 126 iterations in 0.056s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.52  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(t25_zfmisc_1, conjecture,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.21/0.52          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.52        ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.21/0.52             ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t25_zfmisc_1])).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t136_enumset1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ~( ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) & 
% 0.21/0.52          ( ( k4_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ A ) ) !=
% 0.21/0.52            ( k2_tarski @ B @ C ) ) ) ))).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.52         (((X7) = (X6))
% 0.21/0.52          | ((k4_xboole_0 @ (k1_enumset1 @ X7 @ X6 @ X8) @ (k1_tarski @ X7))
% 0.21/0.52              = (k2_tarski @ X6 @ X8))
% 0.21/0.52          | ((X7) = (X8)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t136_enumset1])).
% 0.21/0.52  thf(t38_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.21/0.52       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (![X3 : $i, X4 : $i]:
% 0.21/0.52         (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ (k4_xboole_0 @ X4 @ X3)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (r1_tarski @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0))
% 0.21/0.52          | ((X2) = (X0))
% 0.21/0.52          | ((X2) = (X1))
% 0.21/0.52          | ((k1_tarski @ X2) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.21/0.52        | ((sk_A) = (sk_B))
% 0.21/0.52        | ((sk_A) = (sk_C)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['0', '3'])).
% 0.21/0.52  thf('5', plain, (((sk_A) != (sk_C))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('6', plain, (((sk_A) != (sk_B))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('7', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['4', '5', '6'])).
% 0.21/0.52  thf(t20_zfmisc_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.52         ( k1_tarski @ A ) ) <=>
% 0.21/0.52       ( ( A ) != ( B ) ) ))).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X30 : $i, X31 : $i]:
% 0.21/0.52         (((X31) != (X30))
% 0.21/0.52          | ((k4_xboole_0 @ (k1_tarski @ X31) @ (k1_tarski @ X30))
% 0.21/0.52              != (k1_tarski @ X31)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      (![X30 : $i]:
% 0.21/0.52         ((k4_xboole_0 @ (k1_tarski @ X30) @ (k1_tarski @ X30))
% 0.21/0.52           != (k1_tarski @ X30))),
% 0.21/0.52      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.52  thf(idempotence_k3_xboole_0, axiom,
% 0.21/0.52    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.21/0.52  thf('10', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.21/0.52      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.21/0.52  thf(t100_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (![X1 : $i, X2 : $i]:
% 0.21/0.52         ((k4_xboole_0 @ X1 @ X2)
% 0.21/0.52           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['10', '11'])).
% 0.21/0.52  thf(t92_xboole_1, axiom,
% 0.21/0.52    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.52  thf('13', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ X5) = (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.21/0.52  thf('14', plain, (![X30 : $i]: ((k1_xboole_0) != (k1_tarski @ X30))),
% 0.21/0.52      inference('demod', [status(thm)], ['9', '12', '13'])).
% 0.21/0.52  thf('15', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['7', '14'])).
% 0.21/0.52  thf('16', plain, ($false), inference('simplify', [status(thm)], ['15'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
