%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lTLwJ6ZONS

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   38 (  44 expanded)
%              Number of leaves         :   15 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :  246 ( 312 expanded)
%              Number of equality atoms :   46 (  60 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t66_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
          = k1_xboole_0 )
        & ( A != k1_xboole_0 )
        & ( A
         != ( k1_tarski @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
            = k1_xboole_0 )
          & ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_zfmisc_1])).

thf('0',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('2',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
    = ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('5',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('8',plain,
    ( ( k1_tarski @ sk_B )
    = ( k2_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3','6','7'])).

thf(t44_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ( X18 = X19 )
      | ( ( k1_tarski @ X20 )
       != ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t44_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ sk_B ) )
      | ( sk_A
        = ( k1_tarski @ sk_B ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ sk_B ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['10','11','12'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X14 != X13 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X14 ) @ ( k1_tarski @ X13 ) )
       != ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('15',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X13 ) @ ( k1_tarski @ X13 ) )
     != ( k1_tarski @ X13 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('16',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = k1_xboole_0 ) )).

thf('17',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X16 ) @ ( k2_tarski @ X16 @ X17 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t22_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X13: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X13 ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != ( k1_tarski @ sk_B ) ) ),
    inference(clc,[status(thm)],['13','19'])).

thf('21',plain,(
    $false ),
    inference(eq_res,[status(thm)],['20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lTLwJ6ZONS
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:16:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 23 iterations in 0.016s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.49  thf(t66_zfmisc_1, conjecture,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 0.22/0.49          ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i,B:$i]:
% 0.22/0.49        ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 0.22/0.49             ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t66_zfmisc_1])).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(t39_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      (![X5 : $i, X6 : $i]:
% 0.22/0.49         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 0.22/0.49           = (k2_xboole_0 @ X5 @ X6))),
% 0.22/0.49      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0)
% 0.22/0.49         = (k2_xboole_0 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.22/0.49      inference('sup+', [status(thm)], ['0', '1'])).
% 0.22/0.49  thf(commutativity_k2_xboole_0, axiom,
% 0.22/0.49    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.22/0.49  thf(t1_boole, axiom,
% 0.22/0.49    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.49  thf('5', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.22/0.49      inference('cnf', [status(esa)], [t1_boole])).
% 0.22/0.49  thf('6', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['4', '5'])).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      (((k1_tarski @ sk_B) = (k2_xboole_0 @ sk_A @ (k1_tarski @ sk_B)))),
% 0.22/0.49      inference('demod', [status(thm)], ['2', '3', '6', '7'])).
% 0.22/0.49  thf(t44_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.22/0.49          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.49          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.49         (((X18) = (k1_xboole_0))
% 0.22/0.49          | ((X19) = (k1_xboole_0))
% 0.22/0.49          | ((X18) = (X19))
% 0.22/0.49          | ((k1_tarski @ X20) != (k2_xboole_0 @ X18 @ X19)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t44_zfmisc_1])).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (((k1_tarski @ X0) != (k1_tarski @ sk_B))
% 0.22/0.49          | ((sk_A) = (k1_tarski @ sk_B))
% 0.22/0.49          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.22/0.49          | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.49  thf('11', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('12', plain, (((sk_A) != (k1_tarski @ sk_B))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (((k1_tarski @ X0) != (k1_tarski @ sk_B))
% 0.22/0.49          | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['10', '11', '12'])).
% 0.22/0.49  thf(t20_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.22/0.49         ( k1_tarski @ A ) ) <=>
% 0.22/0.49       ( ( A ) != ( B ) ) ))).
% 0.22/0.49  thf('14', plain,
% 0.22/0.49      (![X13 : $i, X14 : $i]:
% 0.22/0.49         (((X14) != (X13))
% 0.22/0.49          | ((k4_xboole_0 @ (k1_tarski @ X14) @ (k1_tarski @ X13))
% 0.22/0.49              != (k1_tarski @ X14)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      (![X13 : $i]:
% 0.22/0.49         ((k4_xboole_0 @ (k1_tarski @ X13) @ (k1_tarski @ X13))
% 0.22/0.49           != (k1_tarski @ X13))),
% 0.22/0.49      inference('simplify', [status(thm)], ['14'])).
% 0.22/0.49  thf(t69_enumset1, axiom,
% 0.22/0.49    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.49  thf('16', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 0.22/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.49  thf(t22_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.22/0.49       ( k1_xboole_0 ) ))).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      (![X16 : $i, X17 : $i]:
% 0.22/0.49         ((k4_xboole_0 @ (k1_tarski @ X16) @ (k2_tarski @ X16 @ X17))
% 0.22/0.49           = (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [t22_zfmisc_1])).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['16', '17'])).
% 0.22/0.49  thf('19', plain, (![X13 : $i]: ((k1_xboole_0) != (k1_tarski @ X13))),
% 0.22/0.49      inference('demod', [status(thm)], ['15', '18'])).
% 0.22/0.49  thf('20', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_tarski @ sk_B))),
% 0.22/0.49      inference('clc', [status(thm)], ['13', '19'])).
% 0.22/0.49  thf('21', plain, ($false), inference('eq_res', [status(thm)], ['20'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
