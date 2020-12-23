%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Zf6mrjPyKc

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:30 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   35 (  37 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :  185 ( 197 expanded)
%              Number of equality atoms :   12 (  13 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t61_setfam_1,conjecture,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_setfam_1])).

thf('0',plain,(
    ~ ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_zfmisc_1,axiom,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) )).

thf('1',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf(t81_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ X14 ) @ ( k1_zfmisc_1 @ X15 ) ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t81_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

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
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) )
      = ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X16: $i,X18: $i] :
      ( ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    $false ),
    inference(demod,[status(thm)],['0','17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Zf6mrjPyKc
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:32:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 69 iterations in 0.028s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.47  thf(t61_setfam_1, conjecture,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( m1_subset_1 @
% 0.19/0.47       ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (~( ![A:$i]:
% 0.19/0.47        ( m1_subset_1 @
% 0.19/0.47          ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t61_setfam_1])).
% 0.19/0.47  thf('0', plain,
% 0.19/0.47      (~ (m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 0.19/0.47          (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(t1_zfmisc_1, axiom,
% 0.19/0.47    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.19/0.47  thf('1', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.19/0.47      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.19/0.47  thf(t81_zfmisc_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( r1_tarski @
% 0.19/0.47       ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) @ 
% 0.19/0.47       ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.19/0.47  thf('2', plain,
% 0.19/0.47      (![X14 : $i, X15 : $i]:
% 0.19/0.47         (r1_tarski @ 
% 0.19/0.47          (k2_xboole_0 @ (k1_zfmisc_1 @ X14) @ (k1_zfmisc_1 @ X15)) @ 
% 0.19/0.47          (k1_zfmisc_1 @ (k2_xboole_0 @ X14 @ X15)))),
% 0.19/0.47      inference('cnf', [status(esa)], [t81_zfmisc_1])).
% 0.19/0.47  thf('3', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (r1_tarski @ 
% 0.19/0.47          (k2_xboole_0 @ (k1_tarski @ k1_xboole_0) @ (k1_zfmisc_1 @ X0)) @ 
% 0.19/0.47          (k1_zfmisc_1 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.19/0.47      inference('sup+', [status(thm)], ['1', '2'])).
% 0.19/0.47  thf(commutativity_k2_xboole_0, axiom,
% 0.19/0.47    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.19/0.47  thf('4', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.19/0.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.19/0.47  thf(t1_boole, axiom,
% 0.19/0.47    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.19/0.47  thf('5', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.19/0.47      inference('cnf', [status(esa)], [t1_boole])).
% 0.19/0.47  thf('6', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.19/0.47      inference('sup+', [status(thm)], ['4', '5'])).
% 0.19/0.47  thf('7', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (r1_tarski @ 
% 0.19/0.47          (k2_xboole_0 @ (k1_tarski @ k1_xboole_0) @ (k1_zfmisc_1 @ X0)) @ 
% 0.19/0.47          (k1_zfmisc_1 @ X0))),
% 0.19/0.47      inference('demod', [status(thm)], ['3', '6'])).
% 0.19/0.47  thf('8', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.19/0.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.19/0.47  thf(t7_xboole_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.19/0.47  thf('9', plain,
% 0.19/0.47      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 0.19/0.47      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.19/0.47  thf('10', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.19/0.47      inference('sup+', [status(thm)], ['8', '9'])).
% 0.19/0.47  thf(d10_xboole_0, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.47  thf('11', plain,
% 0.19/0.47      (![X2 : $i, X4 : $i]:
% 0.19/0.47         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.19/0.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.47  thf('12', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.19/0.47          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.47  thf('13', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         ((k2_xboole_0 @ (k1_tarski @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))
% 0.19/0.47           = (k1_zfmisc_1 @ X0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['7', '12'])).
% 0.19/0.47  thf('14', plain,
% 0.19/0.47      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 0.19/0.47      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.19/0.47  thf(t3_subset, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.47  thf('15', plain,
% 0.19/0.47      (![X16 : $i, X18 : $i]:
% 0.19/0.47         ((m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X16 @ X18))),
% 0.19/0.47      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.47  thf('16', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.47  thf('17', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 0.19/0.47          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 0.19/0.47      inference('sup+', [status(thm)], ['13', '16'])).
% 0.19/0.47  thf('18', plain, ($false), inference('demod', [status(thm)], ['0', '17'])).
% 0.19/0.47  
% 0.19/0.47  % SZS output end Refutation
% 0.19/0.47  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
