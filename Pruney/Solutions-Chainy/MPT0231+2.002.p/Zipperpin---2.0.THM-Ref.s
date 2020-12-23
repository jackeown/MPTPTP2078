%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mH6tZy2SBy

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:28 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   36 (  45 expanded)
%              Number of leaves         :   12 (  18 expanded)
%              Depth                    :   12
%              Number of atoms          :  191 ( 270 expanded)
%              Number of equality atoms :   25 (  35 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t26_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
     => ( A = C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
       => ( A = C ) ) ),
    inference('cnf.neg',[status(esa)],[t26_zfmisc_1])).

thf('0',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('2',plain,(
    ! [X29: $i,X30: $i] :
      ( ( X30
        = ( k1_tarski @ X29 ) )
      | ( X30 = k1_xboole_0 )
      | ~ ( r1_tarski @ X30 @ ( k1_tarski @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('3',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X32: $i,X33: $i] :
      ( r1_tarski @ ( k1_tarski @ X32 ) @ ( k2_tarski @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf('5',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t6_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf('6',plain,(
    ! [X34: $i,X35: $i] :
      ( ( X35 = X34 )
      | ~ ( r1_tarski @ ( k1_tarski @ X35 ) @ ( k1_tarski @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t6_zfmisc_1])).

thf('7',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_A = sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X32: $i,X33: $i] :
      ( r1_tarski @ ( k1_tarski @ X32 ) @ ( k2_tarski @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf('11',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r1_tarski @ X30 @ ( k1_tarski @ X31 ) )
      | ( X30 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('13',plain,(
    ! [X31: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X31 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X34: $i,X35: $i] :
      ( ( X35 = X34 )
      | ~ ( r1_tarski @ ( k1_tarski @ X35 ) @ ( k1_tarski @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t6_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( sk_A = X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X31: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X31 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('20',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','20'])).

thf('22',plain,(
    $false ),
    inference(simplify,[status(thm)],['21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mH6tZy2SBy
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:54:48 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  % Running portfolio for 600 s
% 0.20/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 29 iterations in 0.019s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.47  thf(t26_zfmisc_1, conjecture,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.20/0.47       ( ( A ) = ( C ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.47        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.20/0.47          ( ( A ) = ( C ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t26_zfmisc_1])).
% 0.20/0.47  thf('0', plain, (((sk_A) != (sk_C))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(l3_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.20/0.47       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X29 : $i, X30 : $i]:
% 0.20/0.47         (((X30) = (k1_tarski @ X29))
% 0.20/0.47          | ((X30) = (k1_xboole_0))
% 0.20/0.47          | ~ (r1_tarski @ X30 @ (k1_tarski @ X29)))),
% 0.20/0.47      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.20/0.47        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.47  thf(t12_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X32 : $i, X33 : $i]:
% 0.20/0.47         (r1_tarski @ (k1_tarski @ X32) @ (k2_tarski @ X32 @ X33))),
% 0.20/0.47      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))
% 0.20/0.47        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.47      inference('sup+', [status(thm)], ['3', '4'])).
% 0.20/0.47  thf(t6_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.20/0.47       ( ( A ) = ( B ) ) ))).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (![X34 : $i, X35 : $i]:
% 0.20/0.47         (((X35) = (X34))
% 0.20/0.47          | ~ (r1_tarski @ (k1_tarski @ X35) @ (k1_tarski @ X34)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t6_zfmisc_1])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)) | ((sk_A) = (sk_C)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.47  thf('8', plain, (((sk_A) != (sk_C))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('9', plain, (((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X32 : $i, X33 : $i]:
% 0.20/0.47         (r1_tarski @ (k1_tarski @ X32) @ (k2_tarski @ X32 @ X33))),
% 0.20/0.47      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.20/0.47  thf('11', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ k1_xboole_0)),
% 0.20/0.47      inference('sup+', [status(thm)], ['9', '10'])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (![X30 : $i, X31 : $i]:
% 0.20/0.47         ((r1_tarski @ X30 @ (k1_tarski @ X31)) | ((X30) != (k1_xboole_0)))),
% 0.20/0.47      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X31 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X31))),
% 0.20/0.47      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.47  thf(d10_xboole_0, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X0 : $i, X2 : $i]:
% 0.20/0.47         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (r1_tarski @ (k1_tarski @ X0) @ k1_xboole_0)
% 0.20/0.47          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.47  thf('16', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['11', '15'])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (![X34 : $i, X35 : $i]:
% 0.20/0.47         (((X35) = (X34))
% 0.20/0.47          | ~ (r1_tarski @ (k1_tarski @ X35) @ (k1_tarski @ X34)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t6_zfmisc_1])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) | ((sk_A) = (X0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      (![X31 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X31))),
% 0.20/0.47      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.47  thf('20', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.20/0.47      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.47  thf('21', plain, (((sk_A) != (sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['0', '20'])).
% 0.20/0.47  thf('22', plain, ($false), inference('simplify', [status(thm)], ['21'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
