%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QyW2MyqDcU

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:41 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   39 (  62 expanded)
%              Number of leaves         :   12 (  22 expanded)
%              Depth                    :   12
%              Number of atoms          :  273 ( 486 expanded)
%              Number of equality atoms :   40 (  73 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X8: $i] :
      ( ( X8
        = ( k1_tarski @ X4 ) )
      | ( ( sk_C @ X8 @ X4 )
        = X4 )
      | ( r2_hidden @ ( sk_C @ X8 @ X4 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X17 )
      | ( r1_tarski @ X18 @ X16 )
      | ( X17
       != ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('2',plain,(
    ! [X16: $i,X18: $i] :
      ( ( r1_tarski @ X18 @ X16 )
      | ~ ( r2_hidden @ X18 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ ( k1_zfmisc_1 @ X0 ) @ X1 )
        = X1 )
      | ( ( k1_zfmisc_1 @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( r1_tarski @ ( sk_C @ ( k1_zfmisc_1 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_zfmisc_1 @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( ( sk_C @ ( k1_zfmisc_1 @ X0 ) @ X1 )
        = X1 )
      | ( ( k4_xboole_0 @ ( sk_C @ ( k1_zfmisc_1 @ X0 ) @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('6',plain,(
    ! [X3: $i] :
      ( ( k4_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ X0 ) )
      | ( ( sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ X0 )
        = X0 )
      | ( ( k1_zfmisc_1 @ k1_xboole_0 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( k1_zfmisc_1 @ k1_xboole_0 )
        = ( k1_tarski @ X0 ) )
      | ( k1_xboole_0
        = ( sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['7'])).

thf('9',plain,
    ( ( k1_xboole_0
      = ( sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ k1_xboole_0 ) )
    | ( ( k1_zfmisc_1 @ k1_xboole_0 )
      = ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t1_zfmisc_1,conjecture,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ( k1_zfmisc_1 @ k1_xboole_0 )
 != ( k1_tarski @ k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t1_zfmisc_1])).

thf('10',plain,(
    ( k1_zfmisc_1 @ k1_xboole_0 )
 != ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( k1_xboole_0
    = ( sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X4: $i,X8: $i] :
      ( ( X8
        = ( k1_tarski @ X4 ) )
      | ( ( sk_C @ X8 @ X4 )
       != X4 )
      | ~ ( r2_hidden @ ( sk_C @ X8 @ X4 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('13',plain,
    ( ~ ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ( ( sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k1_zfmisc_1 @ k1_xboole_0 )
      = ( k1_tarski @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X3: $i] :
      ( ( k4_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r1_tarski @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ( r2_hidden @ X15 @ X17 )
      | ( X17
       != ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('19',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r2_hidden @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,
    ( k1_xboole_0
    = ( sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('22',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_zfmisc_1 @ k1_xboole_0 )
      = ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['13','20','21'])).

thf('23',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ( k1_zfmisc_1 @ k1_xboole_0 )
 != ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QyW2MyqDcU
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:44:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 38 iterations in 0.030s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.48  thf(d1_tarski, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.19/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.19/0.48  thf('0', plain,
% 0.19/0.48      (![X4 : $i, X8 : $i]:
% 0.19/0.48         (((X8) = (k1_tarski @ X4))
% 0.19/0.48          | ((sk_C @ X8 @ X4) = (X4))
% 0.19/0.48          | (r2_hidden @ (sk_C @ X8 @ X4) @ X8))),
% 0.19/0.48      inference('cnf', [status(esa)], [d1_tarski])).
% 0.19/0.48  thf(d1_zfmisc_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.19/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.19/0.48  thf('1', plain,
% 0.19/0.48      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X18 @ X17)
% 0.19/0.48          | (r1_tarski @ X18 @ X16)
% 0.19/0.48          | ((X17) != (k1_zfmisc_1 @ X16)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.19/0.48  thf('2', plain,
% 0.19/0.48      (![X16 : $i, X18 : $i]:
% 0.19/0.48         ((r1_tarski @ X18 @ X16) | ~ (r2_hidden @ X18 @ (k1_zfmisc_1 @ X16)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['1'])).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (((sk_C @ (k1_zfmisc_1 @ X0) @ X1) = (X1))
% 0.19/0.48          | ((k1_zfmisc_1 @ X0) = (k1_tarski @ X1))
% 0.19/0.48          | (r1_tarski @ (sk_C @ (k1_zfmisc_1 @ X0) @ X1) @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['0', '2'])).
% 0.19/0.48  thf(l32_xboole_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.48  thf('4', plain,
% 0.19/0.48      (![X0 : $i, X2 : $i]:
% 0.19/0.48         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.19/0.48      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.19/0.48  thf('5', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (((k1_zfmisc_1 @ X0) = (k1_tarski @ X1))
% 0.19/0.48          | ((sk_C @ (k1_zfmisc_1 @ X0) @ X1) = (X1))
% 0.19/0.48          | ((k4_xboole_0 @ (sk_C @ (k1_zfmisc_1 @ X0) @ X1) @ X0)
% 0.19/0.48              = (k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.48  thf(t3_boole, axiom,
% 0.19/0.48    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.19/0.48  thf('6', plain, (![X3 : $i]: ((k4_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.19/0.48      inference('cnf', [status(esa)], [t3_boole])).
% 0.19/0.48  thf('7', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((k1_xboole_0) = (sk_C @ (k1_zfmisc_1 @ k1_xboole_0) @ X0))
% 0.19/0.48          | ((sk_C @ (k1_zfmisc_1 @ k1_xboole_0) @ X0) = (X0))
% 0.19/0.48          | ((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ X0)))),
% 0.19/0.48      inference('sup+', [status(thm)], ['5', '6'])).
% 0.19/0.48  thf('8', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((X0) != (k1_xboole_0))
% 0.19/0.48          | ((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ X0))
% 0.19/0.48          | ((k1_xboole_0) = (sk_C @ (k1_zfmisc_1 @ k1_xboole_0) @ X0)))),
% 0.19/0.48      inference('eq_fact', [status(thm)], ['7'])).
% 0.19/0.48  thf('9', plain,
% 0.19/0.48      ((((k1_xboole_0) = (sk_C @ (k1_zfmisc_1 @ k1_xboole_0) @ k1_xboole_0))
% 0.19/0.48        | ((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['8'])).
% 0.19/0.48  thf(t1_zfmisc_1, conjecture,
% 0.19/0.48    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (( k1_zfmisc_1 @ k1_xboole_0 ) != ( k1_tarski @ k1_xboole_0 )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t1_zfmisc_1])).
% 0.19/0.48  thf('10', plain,
% 0.19/0.48      (((k1_zfmisc_1 @ k1_xboole_0) != (k1_tarski @ k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('11', plain,
% 0.19/0.48      (((k1_xboole_0) = (sk_C @ (k1_zfmisc_1 @ k1_xboole_0) @ k1_xboole_0))),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.19/0.48  thf('12', plain,
% 0.19/0.48      (![X4 : $i, X8 : $i]:
% 0.19/0.48         (((X8) = (k1_tarski @ X4))
% 0.19/0.48          | ((sk_C @ X8 @ X4) != (X4))
% 0.19/0.48          | ~ (r2_hidden @ (sk_C @ X8 @ X4) @ X8))),
% 0.19/0.48      inference('cnf', [status(esa)], [d1_tarski])).
% 0.19/0.48  thf('13', plain,
% 0.19/0.48      ((~ (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.19/0.48        | ((sk_C @ (k1_zfmisc_1 @ k1_xboole_0) @ k1_xboole_0) != (k1_xboole_0))
% 0.19/0.48        | ((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.48  thf('14', plain, (![X3 : $i]: ((k4_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.19/0.48      inference('cnf', [status(esa)], [t3_boole])).
% 0.19/0.48  thf('15', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.19/0.48  thf('16', plain,
% 0.19/0.48      (![X0 : $i]: (((X0) != (k1_xboole_0)) | (r1_tarski @ X0 @ k1_xboole_0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.48  thf('17', plain, ((r1_tarski @ k1_xboole_0 @ k1_xboole_0)),
% 0.19/0.48      inference('simplify', [status(thm)], ['16'])).
% 0.19/0.48  thf('18', plain,
% 0.19/0.48      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.19/0.48         (~ (r1_tarski @ X15 @ X16)
% 0.19/0.48          | (r2_hidden @ X15 @ X17)
% 0.19/0.48          | ((X17) != (k1_zfmisc_1 @ X16)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.19/0.48  thf('19', plain,
% 0.19/0.48      (![X15 : $i, X16 : $i]:
% 0.19/0.48         ((r2_hidden @ X15 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X15 @ X16))),
% 0.19/0.48      inference('simplify', [status(thm)], ['18'])).
% 0.19/0.48  thf('20', plain, ((r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['17', '19'])).
% 0.19/0.48  thf('21', plain,
% 0.19/0.48      (((k1_xboole_0) = (sk_C @ (k1_zfmisc_1 @ k1_xboole_0) @ k1_xboole_0))),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.19/0.48  thf('22', plain,
% 0.19/0.48      ((((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.48        | ((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0)))),
% 0.19/0.48      inference('demod', [status(thm)], ['13', '20', '21'])).
% 0.19/0.48  thf('23', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.19/0.48      inference('simplify', [status(thm)], ['22'])).
% 0.19/0.48  thf('24', plain,
% 0.19/0.48      (((k1_zfmisc_1 @ k1_xboole_0) != (k1_tarski @ k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('25', plain, ($false),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
