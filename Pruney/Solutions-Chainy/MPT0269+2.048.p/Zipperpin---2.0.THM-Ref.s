%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.R9bp9bkjmW

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   28 (  34 expanded)
%              Number of leaves         :   13 (  16 expanded)
%              Depth                    :    8
%              Number of atoms          :  134 ( 212 expanded)
%              Number of equality atoms :   19 (  37 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k4_xboole_0 @ X22 @ ( k1_tarski @ X23 ) )
        = X22 )
      | ( r2_hidden @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('2',plain,
    ( ( k1_xboole_0 = sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['2','3'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('5',plain,(
    ! [X16: $i,X18: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X16 ) @ X18 )
      | ~ ( r2_hidden @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('6',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t45_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( B
        = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) ) )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('8',plain,
    ( sk_A
    = ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('11',plain,
    ( sk_A
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.R9bp9bkjmW
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:04:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 31 iterations in 0.015s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.46  thf(t66_zfmisc_1, conjecture,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 0.21/0.46          ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i,B:$i]:
% 0.21/0.46        ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 0.21/0.46             ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t66_zfmisc_1])).
% 0.21/0.46  thf('0', plain,
% 0.21/0.46      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t65_zfmisc_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.21/0.46       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.21/0.46  thf('1', plain,
% 0.21/0.46      (![X22 : $i, X23 : $i]:
% 0.21/0.46         (((k4_xboole_0 @ X22 @ (k1_tarski @ X23)) = (X22))
% 0.21/0.46          | (r2_hidden @ X23 @ X22))),
% 0.21/0.46      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.21/0.46  thf('2', plain, ((((k1_xboole_0) = (sk_A)) | (r2_hidden @ sk_B @ sk_A))),
% 0.21/0.46      inference('sup+', [status(thm)], ['0', '1'])).
% 0.21/0.46  thf('3', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('4', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.21/0.46      inference('simplify_reflect-', [status(thm)], ['2', '3'])).
% 0.21/0.46  thf(l1_zfmisc_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.21/0.46  thf('5', plain,
% 0.21/0.46      (![X16 : $i, X18 : $i]:
% 0.21/0.46         ((r1_tarski @ (k1_tarski @ X16) @ X18) | ~ (r2_hidden @ X16 @ X18))),
% 0.21/0.46      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.46  thf('6', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ sk_A)),
% 0.21/0.46      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.46  thf(t45_xboole_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( r1_tarski @ A @ B ) =>
% 0.21/0.46       ( ( B ) = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ))).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      (![X4 : $i, X5 : $i]:
% 0.21/0.46         (((X5) = (k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4)))
% 0.21/0.46          | ~ (r1_tarski @ X4 @ X5))),
% 0.21/0.46      inference('cnf', [status(esa)], [t45_xboole_1])).
% 0.21/0.46  thf('8', plain,
% 0.21/0.46      (((sk_A)
% 0.21/0.46         = (k2_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.21/0.46            (k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.46  thf('9', plain,
% 0.21/0.46      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t1_boole, axiom,
% 0.21/0.46    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.46  thf('10', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.21/0.46      inference('cnf', [status(esa)], [t1_boole])).
% 0.21/0.46  thf('11', plain, (((sk_A) = (k1_tarski @ sk_B))),
% 0.21/0.46      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.21/0.46  thf('12', plain, (((sk_A) != (k1_tarski @ sk_B))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('13', plain, ($false),
% 0.21/0.46      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
