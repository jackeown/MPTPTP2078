%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9cMwrIH7iE

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:31 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   29 (  34 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    8
%              Number of atoms          :  135 ( 168 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('2',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ X29 @ X30 )
      | ( r2_hidden @ X29 @ X31 )
      | ( X31
       != ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('3',plain,(
    ! [X29: $i,X30: $i] :
      ( ( r2_hidden @ X29 @ ( k1_zfmisc_1 @ X30 ) )
      | ~ ( r1_tarski @ X29 @ X30 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X34: $i,X36: $i,X37: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X34 @ X36 ) @ X37 )
      | ~ ( r2_hidden @ X36 @ X37 )
      | ~ ( r2_hidden @ X34 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_tarski @ k1_xboole_0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('9',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X38: $i,X40: $i] :
      ( ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X40 ) )
      | ~ ( r1_tarski @ X38 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    $false ),
    inference(demod,[status(thm)],['0','12'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9cMwrIH7iE
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:21:18 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 32 iterations in 0.016s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.46  thf(t61_setfam_1, conjecture,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( m1_subset_1 @
% 0.19/0.46       ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i]:
% 0.19/0.46        ( m1_subset_1 @
% 0.19/0.46          ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t61_setfam_1])).
% 0.19/0.46  thf('0', plain,
% 0.19/0.46      (~ (m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 0.19/0.46          (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.19/0.46  thf('1', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.19/0.46      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.46  thf(d1_zfmisc_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.19/0.46       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.19/0.46  thf('2', plain,
% 0.19/0.46      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.19/0.46         (~ (r1_tarski @ X29 @ X30)
% 0.19/0.46          | (r2_hidden @ X29 @ X31)
% 0.19/0.46          | ((X31) != (k1_zfmisc_1 @ X30)))),
% 0.19/0.46      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.19/0.46  thf('3', plain,
% 0.19/0.46      (![X29 : $i, X30 : $i]:
% 0.19/0.46         ((r2_hidden @ X29 @ (k1_zfmisc_1 @ X30)) | ~ (r1_tarski @ X29 @ X30))),
% 0.19/0.46      inference('simplify', [status(thm)], ['2'])).
% 0.19/0.46  thf('4', plain, (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.19/0.46      inference('sup-', [status(thm)], ['1', '3'])).
% 0.19/0.46  thf('5', plain, (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.19/0.46      inference('sup-', [status(thm)], ['1', '3'])).
% 0.19/0.46  thf(t38_zfmisc_1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.19/0.46       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.19/0.46  thf('6', plain,
% 0.19/0.46      (![X34 : $i, X36 : $i, X37 : $i]:
% 0.19/0.46         ((r1_tarski @ (k2_tarski @ X34 @ X36) @ X37)
% 0.19/0.46          | ~ (r2_hidden @ X36 @ X37)
% 0.19/0.46          | ~ (r2_hidden @ X34 @ X37))),
% 0.19/0.46      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.19/0.46  thf('7', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         (~ (r2_hidden @ X1 @ (k1_zfmisc_1 @ X0))
% 0.19/0.46          | (r1_tarski @ (k2_tarski @ X1 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.46  thf('8', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (r1_tarski @ (k2_tarski @ k1_xboole_0 @ k1_xboole_0) @ 
% 0.19/0.46          (k1_zfmisc_1 @ X0))),
% 0.19/0.46      inference('sup-', [status(thm)], ['4', '7'])).
% 0.19/0.46  thf(t69_enumset1, axiom,
% 0.19/0.46    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.46  thf('9', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.19/0.46      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.46  thf('10', plain,
% 0.19/0.46      (![X0 : $i]: (r1_tarski @ (k1_tarski @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.19/0.46      inference('demod', [status(thm)], ['8', '9'])).
% 0.19/0.46  thf(t3_subset, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.46  thf('11', plain,
% 0.19/0.46      (![X38 : $i, X40 : $i]:
% 0.19/0.46         ((m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X40)) | ~ (r1_tarski @ X38 @ X40))),
% 0.19/0.46      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.46  thf('12', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 0.19/0.46          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.46  thf('13', plain, ($false), inference('demod', [status(thm)], ['0', '12'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.32/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
