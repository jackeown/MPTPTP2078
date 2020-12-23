%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EytMvGiz0T

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   26 (  31 expanded)
%              Number of leaves         :   11 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :  148 ( 202 expanded)
%              Number of equality atoms :    9 (  13 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t27_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
     => ( ( k2_tarski @ A @ B )
        = ( k1_tarski @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
       => ( ( k2_tarski @ A @ B )
          = ( k1_tarski @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_zfmisc_1])).

thf('0',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_C ) @ ( k2_tarski @ sk_A @ sk_B ) )
    | ( ( k1_tarski @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k1_tarski @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k1_tarski @ sk_C ) @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X28: $i,X29: $i] :
      ( r1_tarski @ ( k1_tarski @ X28 ) @ ( k2_tarski @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_tarski @ X14 @ X15 )
      | ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X1 ) @ X2 )
      | ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf(t24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf('10',plain,(
    ! [X30: $i,X31: $i] :
      ( ( X31 = X30 )
      | ~ ( r1_tarski @ ( k1_tarski @ X31 ) @ ( k1_tarski @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t24_zfmisc_1])).

thf('11',plain,(
    sk_A = sk_C ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X28: $i,X29: $i] :
      ( r1_tarski @ ( k1_tarski @ X28 ) @ ( k2_tarski @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf('13',plain,(
    $false ),
    inference(demod,[status(thm)],['4','11','12'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EytMvGiz0T
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:40:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 172 iterations in 0.084s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.53  thf(t27_zfmisc_1, conjecture,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.21/0.53       ( ( k2_tarski @ A @ B ) = ( k1_tarski @ C ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.53        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.21/0.53          ( ( k2_tarski @ A @ B ) = ( k1_tarski @ C ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t27_zfmisc_1])).
% 0.21/0.53  thf('0', plain,
% 0.21/0.53      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(d10_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X2 : $i, X4 : $i]:
% 0.21/0.53         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.21/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      ((~ (r1_tarski @ (k1_tarski @ sk_C) @ (k2_tarski @ sk_A @ sk_B))
% 0.21/0.53        | ((k1_tarski @ sk_C) = (k2_tarski @ sk_A @ sk_B)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.53  thf('3', plain, (((k2_tarski @ sk_A @ sk_B) != (k1_tarski @ sk_C))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (~ (r1_tarski @ (k1_tarski @ sk_C) @ (k2_tarski @ sk_A @ sk_B))),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['2', '3'])).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t12_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X28 : $i, X29 : $i]:
% 0.21/0.53         (r1_tarski @ (k1_tarski @ X28) @ (k2_tarski @ X28 @ X29))),
% 0.21/0.53      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.21/0.53  thf(t1_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.53       ( r1_tarski @ A @ C ) ))).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.53         (~ (r1_tarski @ X13 @ X14)
% 0.21/0.53          | ~ (r1_tarski @ X14 @ X15)
% 0.21/0.53          | (r1_tarski @ X13 @ X15))),
% 0.21/0.53      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         ((r1_tarski @ (k1_tarski @ X1) @ X2)
% 0.21/0.53          | ~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X2))),
% 0.21/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.53  thf('9', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))),
% 0.21/0.53      inference('sup-', [status(thm)], ['5', '8'])).
% 0.21/0.53  thf(t24_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.21/0.53       ( ( A ) = ( B ) ) ))).
% 0.21/0.54  thf('10', plain,
% 0.21/0.54      (![X30 : $i, X31 : $i]:
% 0.21/0.54         (((X31) = (X30))
% 0.21/0.54          | ~ (r1_tarski @ (k1_tarski @ X31) @ (k1_tarski @ X30)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t24_zfmisc_1])).
% 0.21/0.54  thf('11', plain, (((sk_A) = (sk_C))),
% 0.21/0.54      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.54  thf('12', plain,
% 0.21/0.54      (![X28 : $i, X29 : $i]:
% 0.21/0.54         (r1_tarski @ (k1_tarski @ X28) @ (k2_tarski @ X28 @ X29))),
% 0.21/0.54      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.21/0.54  thf('13', plain, ($false),
% 0.21/0.54      inference('demod', [status(thm)], ['4', '11', '12'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
