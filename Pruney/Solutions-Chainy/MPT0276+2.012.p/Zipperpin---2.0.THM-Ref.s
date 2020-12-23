%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JDnskTFhMK

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   22 (  28 expanded)
%              Number of leaves         :   11 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :  234 ( 426 expanded)
%              Number of equality atoms :   31 (  55 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( X4
        = ( k2_tarski @ X2 @ X3 ) )
      | ( X4
        = ( k1_tarski @ X3 ) )
      | ( X4
        = ( k1_tarski @ X2 ) )
      | ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ ( k2_tarski @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
        = ( k1_tarski @ X1 ) )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
        = ( k1_tarski @ X0 ) )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
        = ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t74_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
         != k1_xboole_0 )
        & ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
         != ( k1_tarski @ A ) )
        & ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
         != ( k1_tarski @ B ) )
        & ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
         != ( k2_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
           != k1_xboole_0 )
          & ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
           != ( k1_tarski @ A ) )
          & ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
           != ( k1_tarski @ B ) )
          & ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
           != ( k2_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t74_zfmisc_1])).

thf('3',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k1_tarski @ sk_B ) )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k1_tarski @ sk_B ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
 != ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['5','6','7','8'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JDnskTFhMK
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:22:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.46  % Solved by: fo/fo7.sh
% 0.22/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.46  % done 10 iterations in 0.008s
% 0.22/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.46  % SZS output start Refutation
% 0.22/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.46  thf(t36_xboole_1, axiom,
% 0.22/0.46    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.22/0.46  thf('0', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.22/0.46      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.22/0.46  thf(l45_zfmisc_1, axiom,
% 0.22/0.46    (![A:$i,B:$i,C:$i]:
% 0.22/0.46     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.22/0.46       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.22/0.46            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.22/0.46  thf('1', plain,
% 0.22/0.46      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.46         (((X4) = (k2_tarski @ X2 @ X3))
% 0.22/0.46          | ((X4) = (k1_tarski @ X3))
% 0.22/0.46          | ((X4) = (k1_tarski @ X2))
% 0.22/0.46          | ((X4) = (k1_xboole_0))
% 0.22/0.46          | ~ (r1_tarski @ X4 @ (k2_tarski @ X2 @ X3)))),
% 0.22/0.46      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.22/0.46  thf('2', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.46         (((k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2) = (k1_xboole_0))
% 0.22/0.46          | ((k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2) = (k1_tarski @ X1))
% 0.22/0.46          | ((k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2) = (k1_tarski @ X0))
% 0.22/0.46          | ((k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2) = (k2_tarski @ X1 @ X0)))),
% 0.22/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.46  thf(t74_zfmisc_1, conjecture,
% 0.22/0.46    (![A:$i,B:$i,C:$i]:
% 0.22/0.46     ( ~( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) & 
% 0.22/0.46          ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_tarski @ A ) ) & 
% 0.22/0.46          ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_tarski @ B ) ) & 
% 0.22/0.46          ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) !=
% 0.22/0.46            ( k2_tarski @ A @ B ) ) ) ))).
% 0.22/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.46    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.46        ( ~( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) & 
% 0.22/0.46             ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_tarski @ A ) ) & 
% 0.22/0.46             ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_tarski @ B ) ) & 
% 0.22/0.46             ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) !=
% 0.22/0.46               ( k2_tarski @ A @ B ) ) ) ) )),
% 0.22/0.46    inference('cnf.neg', [status(esa)], [t74_zfmisc_1])).
% 0.22/0.46  thf('3', plain,
% 0.22/0.46      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.22/0.46         != (k2_tarski @ sk_A @ sk_B))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('4', plain,
% 0.22/0.46      ((((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))
% 0.22/0.46        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.22/0.46            = (k1_tarski @ sk_B))
% 0.22/0.46        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.22/0.46            = (k1_tarski @ sk_A))
% 0.22/0.46        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0)))),
% 0.22/0.46      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.46  thf('5', plain,
% 0.22/0.46      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))
% 0.22/0.46        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.22/0.46            = (k1_tarski @ sk_A))
% 0.22/0.46        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.22/0.46            = (k1_tarski @ sk_B)))),
% 0.22/0.46      inference('simplify', [status(thm)], ['4'])).
% 0.22/0.46  thf('6', plain,
% 0.22/0.46      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) != (k1_tarski @ sk_B))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('7', plain,
% 0.22/0.46      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) != (k1_tarski @ sk_A))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('8', plain,
% 0.22/0.46      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) != (k1_xboole_0))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('9', plain, ($false),
% 0.22/0.46      inference('simplify_reflect-', [status(thm)], ['5', '6', '7', '8'])).
% 0.22/0.46  
% 0.22/0.46  % SZS output end Refutation
% 0.22/0.46  
% 0.22/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
