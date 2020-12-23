%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TtcXM8JD3n

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:41 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   27 (  31 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :  134 ( 194 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t8_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ C @ D ) )
     => ( m1_subset_1 @ ( k1_tarski @ ( k4_tarski @ A @ C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ C @ D ) )
       => ( m1_subset_1 @ ( k1_tarski @ ( k4_tarski @ A @ C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_relset_1])).

thf('0',plain,(
    ~ ( m1_subset_1 @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r2_hidden @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X4 @ X6 ) @ ( k2_zfmisc_1 @ X5 @ X8 ) )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ sk_C ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_C ) @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('6',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X1 ) @ X3 )
      | ~ ( r2_hidden @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('7',plain,(
    r1_tarski @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_C ) ) @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('9',plain,(
    m1_subset_1 @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    $false ),
    inference(demod,[status(thm)],['0','9'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TtcXM8JD3n
% 0.11/0.32  % Computer   : n021.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 18:31:19 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running portfolio for 600 s
% 0.11/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.11/0.33  % Number of cores: 8
% 0.11/0.33  % Python version: Python 3.6.8
% 0.11/0.33  % Running in FO mode
% 0.18/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.18/0.47  % Solved by: fo/fo7.sh
% 0.18/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.47  % done 47 iterations in 0.020s
% 0.18/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.18/0.47  % SZS output start Refutation
% 0.18/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.18/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.18/0.47  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.18/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.18/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.18/0.47  thf(sk_D_type, type, sk_D: $i).
% 0.18/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.18/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.18/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.18/0.47  thf(t8_relset_1, conjecture,
% 0.18/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.18/0.47     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ D ) ) =>
% 0.18/0.47       ( m1_subset_1 @
% 0.18/0.47         ( k1_tarski @ ( k4_tarski @ A @ C ) ) @ 
% 0.18/0.47         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ D ) ) ) ))).
% 0.18/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.47    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.18/0.47        ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ D ) ) =>
% 0.18/0.47          ( m1_subset_1 @
% 0.18/0.47            ( k1_tarski @ ( k4_tarski @ A @ C ) ) @ 
% 0.18/0.47            ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ D ) ) ) ) )),
% 0.18/0.47    inference('cnf.neg', [status(esa)], [t8_relset_1])).
% 0.18/0.47  thf('0', plain,
% 0.18/0.47      (~ (m1_subset_1 @ (k1_tarski @ (k4_tarski @ sk_A @ sk_C)) @ 
% 0.18/0.47          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_D)))),
% 0.18/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.47  thf('1', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.18/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.47  thf('2', plain, ((r2_hidden @ sk_C @ sk_D)),
% 0.18/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.47  thf(l54_zfmisc_1, axiom,
% 0.18/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.18/0.47     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.18/0.47       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.18/0.47  thf('3', plain,
% 0.18/0.47      (![X4 : $i, X5 : $i, X6 : $i, X8 : $i]:
% 0.18/0.47         ((r2_hidden @ (k4_tarski @ X4 @ X6) @ (k2_zfmisc_1 @ X5 @ X8))
% 0.18/0.47          | ~ (r2_hidden @ X6 @ X8)
% 0.18/0.47          | ~ (r2_hidden @ X4 @ X5))),
% 0.18/0.47      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.18/0.47  thf('4', plain,
% 0.18/0.47      (![X0 : $i, X1 : $i]:
% 0.18/0.47         (~ (r2_hidden @ X1 @ X0)
% 0.18/0.47          | (r2_hidden @ (k4_tarski @ X1 @ sk_C) @ (k2_zfmisc_1 @ X0 @ sk_D)))),
% 0.18/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.18/0.47  thf('5', plain,
% 0.18/0.47      ((r2_hidden @ (k4_tarski @ sk_A @ sk_C) @ (k2_zfmisc_1 @ sk_B @ sk_D))),
% 0.18/0.47      inference('sup-', [status(thm)], ['1', '4'])).
% 0.18/0.47  thf(l1_zfmisc_1, axiom,
% 0.18/0.47    (![A:$i,B:$i]:
% 0.18/0.47     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.18/0.47  thf('6', plain,
% 0.18/0.47      (![X1 : $i, X3 : $i]:
% 0.18/0.47         ((r1_tarski @ (k1_tarski @ X1) @ X3) | ~ (r2_hidden @ X1 @ X3))),
% 0.18/0.47      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.18/0.47  thf('7', plain,
% 0.18/0.47      ((r1_tarski @ (k1_tarski @ (k4_tarski @ sk_A @ sk_C)) @ 
% 0.18/0.47        (k2_zfmisc_1 @ sk_B @ sk_D))),
% 0.18/0.47      inference('sup-', [status(thm)], ['5', '6'])).
% 0.18/0.47  thf(t3_subset, axiom,
% 0.18/0.47    (![A:$i,B:$i]:
% 0.18/0.47     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.18/0.47  thf('8', plain,
% 0.18/0.47      (![X9 : $i, X11 : $i]:
% 0.18/0.47         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 0.18/0.47      inference('cnf', [status(esa)], [t3_subset])).
% 0.18/0.47  thf('9', plain,
% 0.18/0.47      ((m1_subset_1 @ (k1_tarski @ (k4_tarski @ sk_A @ sk_C)) @ 
% 0.18/0.47        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_D)))),
% 0.18/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.18/0.47  thf('10', plain, ($false), inference('demod', [status(thm)], ['0', '9'])).
% 0.18/0.47  
% 0.18/0.47  % SZS output end Refutation
% 0.18/0.47  
% 0.18/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
