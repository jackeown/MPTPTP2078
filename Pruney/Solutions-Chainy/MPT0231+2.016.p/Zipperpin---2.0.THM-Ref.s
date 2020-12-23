%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YAcJ66Iuun

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:30 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   37 (  59 expanded)
%              Number of leaves         :   13 (  23 expanded)
%              Depth                    :   12
%              Number of atoms          :  200 ( 377 expanded)
%              Number of equality atoms :   26 (  47 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X35: $i,X36: $i] :
      ( ( X36
        = ( k1_tarski @ X35 ) )
      | ( X36 = k1_xboole_0 )
      | ~ ( r1_tarski @ X36 @ ( k1_tarski @ X35 ) ) ) ),
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
    ! [X38: $i,X39: $i] :
      ( r1_tarski @ ( k1_tarski @ X38 ) @ ( k2_tarski @ X38 @ X39 ) ) ),
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
    ! [X40: $i,X41: $i] :
      ( ( X41 = X40 )
      | ~ ( r1_tarski @ ( k1_tarski @ X41 ) @ ( k1_tarski @ X40 ) ) ) ),
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
    ! [X38: $i,X39: $i] :
      ( r1_tarski @ ( k1_tarski @ X38 ) @ ( k2_tarski @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ sk_A ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('14',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('15',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('16',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ! [X40: $i,X41: $i] :
      ( ( X41 = X40 )
      | ~ ( r1_tarski @ ( k1_tarski @ X41 ) @ ( k1_tarski @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t6_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( sk_A = X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

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
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YAcJ66Iuun
% 0.14/0.36  % Computer   : n017.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 17:31:17 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 42 iterations in 0.037s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.51  thf(t26_zfmisc_1, conjecture,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.22/0.51       ( ( A ) = ( C ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.51        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.22/0.51          ( ( A ) = ( C ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t26_zfmisc_1])).
% 0.22/0.51  thf('0', plain, (((sk_A) != (sk_C))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('1', plain,
% 0.22/0.51      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(l3_zfmisc_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.22/0.51       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.22/0.51  thf('2', plain,
% 0.22/0.51      (![X35 : $i, X36 : $i]:
% 0.22/0.51         (((X36) = (k1_tarski @ X35))
% 0.22/0.51          | ((X36) = (k1_xboole_0))
% 0.22/0.51          | ~ (r1_tarski @ X36 @ (k1_tarski @ X35)))),
% 0.22/0.51      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.22/0.51  thf('3', plain,
% 0.22/0.51      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.22/0.51        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.51  thf(t12_zfmisc_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.22/0.51  thf('4', plain,
% 0.22/0.51      (![X38 : $i, X39 : $i]:
% 0.22/0.51         (r1_tarski @ (k1_tarski @ X38) @ (k2_tarski @ X38 @ X39))),
% 0.22/0.51      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.22/0.51  thf('5', plain,
% 0.22/0.51      (((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))
% 0.22/0.51        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.22/0.51      inference('sup+', [status(thm)], ['3', '4'])).
% 0.22/0.51  thf(t6_zfmisc_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.22/0.51       ( ( A ) = ( B ) ) ))).
% 0.22/0.51  thf('6', plain,
% 0.22/0.51      (![X40 : $i, X41 : $i]:
% 0.22/0.51         (((X41) = (X40))
% 0.22/0.51          | ~ (r1_tarski @ (k1_tarski @ X41) @ (k1_tarski @ X40)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t6_zfmisc_1])).
% 0.22/0.51  thf('7', plain,
% 0.22/0.51      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)) | ((sk_A) = (sk_C)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.51  thf('8', plain, (((sk_A) != (sk_C))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('9', plain, (((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.22/0.51      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.22/0.51  thf('10', plain,
% 0.22/0.51      (![X38 : $i, X39 : $i]:
% 0.22/0.51         (r1_tarski @ (k1_tarski @ X38) @ (k2_tarski @ X38 @ X39))),
% 0.22/0.51      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.22/0.51  thf(d10_xboole_0, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.51  thf('11', plain,
% 0.22/0.51      (![X5 : $i, X7 : $i]:
% 0.22/0.51         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 0.22/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.51  thf('12', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 0.22/0.51          | ((k2_tarski @ X1 @ X0) = (k1_tarski @ X1)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.51  thf('13', plain,
% 0.22/0.51      ((~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ sk_A))
% 0.22/0.51        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['9', '12'])).
% 0.22/0.51  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.51  thf('14', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.22/0.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.51  thf('15', plain, (((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.22/0.51      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.22/0.51  thf('16', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.22/0.51  thf('17', plain,
% 0.22/0.51      (![X40 : $i, X41 : $i]:
% 0.22/0.51         (((X41) = (X40))
% 0.22/0.51          | ~ (r1_tarski @ (k1_tarski @ X41) @ (k1_tarski @ X40)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t6_zfmisc_1])).
% 0.22/0.51  thf('18', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) | ((sk_A) = (X0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.51  thf('19', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.22/0.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.51  thf('20', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.22/0.51      inference('demod', [status(thm)], ['18', '19'])).
% 0.22/0.51  thf('21', plain, (((sk_A) != (sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['0', '20'])).
% 0.22/0.51  thf('22', plain, ($false), inference('simplify', [status(thm)], ['21'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
