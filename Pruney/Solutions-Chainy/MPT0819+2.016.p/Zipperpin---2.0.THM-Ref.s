%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.z8obtVKELc

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:47 EST 2020

% Result     : Theorem 0.78s
% Output     : Refutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :   37 (  44 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :  230 ( 345 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(t17_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ C @ D ) )
       => ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
       => ( ( ( r1_tarski @ A @ B )
            & ( r1_tarski @ C @ D ) )
         => ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_relset_1])).

thf('0',plain,(
    ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('3',plain,(
    r1_tarski @ sk_E @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ( X5
       != ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    r2_hidden @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    r1_tarski @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r1_tarski @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t119_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D ) )
     => ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X8 @ X10 ) @ ( k2_zfmisc_1 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t119_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ X1 ) @ ( k2_zfmisc_1 @ sk_B_2 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) @ ( k2_zfmisc_1 @ sk_B_2 @ sk_D ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(t79_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X12 ) @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('13',plain,(
    r1_tarski @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X17: $i,X19: $i] :
      ( ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,(
    m1_subset_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('16',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( m1_subset_1 @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_D ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['0','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.z8obtVKELc
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:03:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.78/1.00  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.78/1.00  % Solved by: fo/fo7.sh
% 0.78/1.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.78/1.00  % done 934 iterations in 0.542s
% 0.78/1.00  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.78/1.00  % SZS output start Refutation
% 0.78/1.00  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.78/1.00  thf(sk_A_type, type, sk_A: $i).
% 0.78/1.00  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.78/1.00  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.78/1.00  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.78/1.00  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.78/1.00  thf(sk_D_type, type, sk_D: $i).
% 0.78/1.00  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.78/1.00  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.78/1.00  thf(sk_E_type, type, sk_E: $i).
% 0.78/1.00  thf(t17_relset_1, conjecture,
% 0.78/1.00    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.78/1.00     ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.78/1.00       ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.78/1.00         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ D ) ) ) ) ))).
% 0.78/1.00  thf(zf_stmt_0, negated_conjecture,
% 0.78/1.00    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.78/1.00        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.78/1.00          ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.78/1.00            ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ D ) ) ) ) ) )),
% 0.78/1.00    inference('cnf.neg', [status(esa)], [t17_relset_1])).
% 0.78/1.00  thf('0', plain,
% 0.78/1.00      (~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_D)))),
% 0.78/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.00  thf('1', plain,
% 0.78/1.00      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.78/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.00  thf(t3_subset, axiom,
% 0.78/1.00    (![A:$i,B:$i]:
% 0.78/1.00     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.78/1.00  thf('2', plain,
% 0.78/1.00      (![X17 : $i, X18 : $i]:
% 0.78/1.00         ((r1_tarski @ X17 @ X18) | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 0.78/1.00      inference('cnf', [status(esa)], [t3_subset])).
% 0.78/1.00  thf('3', plain, ((r1_tarski @ sk_E @ (k2_zfmisc_1 @ sk_A @ sk_C_1))),
% 0.78/1.00      inference('sup-', [status(thm)], ['1', '2'])).
% 0.78/1.00  thf(d1_zfmisc_1, axiom,
% 0.78/1.00    (![A:$i,B:$i]:
% 0.78/1.00     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.78/1.00       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.78/1.00  thf('4', plain,
% 0.78/1.00      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.78/1.00         (~ (r1_tarski @ X3 @ X4)
% 0.78/1.00          | (r2_hidden @ X3 @ X5)
% 0.78/1.00          | ((X5) != (k1_zfmisc_1 @ X4)))),
% 0.78/1.00      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.78/1.00  thf('5', plain,
% 0.78/1.00      (![X3 : $i, X4 : $i]:
% 0.78/1.00         ((r2_hidden @ X3 @ (k1_zfmisc_1 @ X4)) | ~ (r1_tarski @ X3 @ X4))),
% 0.78/1.00      inference('simplify', [status(thm)], ['4'])).
% 0.78/1.00  thf('6', plain,
% 0.78/1.00      ((r2_hidden @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.78/1.00      inference('sup-', [status(thm)], ['3', '5'])).
% 0.78/1.00  thf('7', plain, ((r1_tarski @ sk_C_1 @ sk_D)),
% 0.78/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.00  thf('8', plain, ((r1_tarski @ sk_A @ sk_B_2)),
% 0.78/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/1.00  thf(t119_zfmisc_1, axiom,
% 0.78/1.00    (![A:$i,B:$i,C:$i,D:$i]:
% 0.78/1.00     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.78/1.00       ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.78/1.00  thf('9', plain,
% 0.78/1.00      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.78/1.00         (~ (r1_tarski @ X8 @ X9)
% 0.78/1.00          | ~ (r1_tarski @ X10 @ X11)
% 0.78/1.00          | (r1_tarski @ (k2_zfmisc_1 @ X8 @ X10) @ (k2_zfmisc_1 @ X9 @ X11)))),
% 0.78/1.00      inference('cnf', [status(esa)], [t119_zfmisc_1])).
% 0.78/1.00  thf('10', plain,
% 0.78/1.00      (![X0 : $i, X1 : $i]:
% 0.78/1.00         ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ X1) @ (k2_zfmisc_1 @ sk_B_2 @ X0))
% 0.78/1.00          | ~ (r1_tarski @ X1 @ X0))),
% 0.78/1.00      inference('sup-', [status(thm)], ['8', '9'])).
% 0.78/1.00  thf('11', plain,
% 0.78/1.00      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_C_1) @ 
% 0.78/1.00        (k2_zfmisc_1 @ sk_B_2 @ sk_D))),
% 0.78/1.00      inference('sup-', [status(thm)], ['7', '10'])).
% 0.78/1.00  thf(t79_zfmisc_1, axiom,
% 0.78/1.00    (![A:$i,B:$i]:
% 0.78/1.00     ( ( r1_tarski @ A @ B ) =>
% 0.78/1.00       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.78/1.00  thf('12', plain,
% 0.78/1.00      (![X12 : $i, X13 : $i]:
% 0.78/1.00         ((r1_tarski @ (k1_zfmisc_1 @ X12) @ (k1_zfmisc_1 @ X13))
% 0.78/1.00          | ~ (r1_tarski @ X12 @ X13))),
% 0.78/1.00      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 0.78/1.00  thf('13', plain,
% 0.78/1.00      ((r1_tarski @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)) @ 
% 0.78/1.00        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_D)))),
% 0.78/1.00      inference('sup-', [status(thm)], ['11', '12'])).
% 0.78/1.00  thf('14', plain,
% 0.78/1.00      (![X17 : $i, X19 : $i]:
% 0.78/1.00         ((m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X17 @ X19))),
% 0.78/1.00      inference('cnf', [status(esa)], [t3_subset])).
% 0.78/1.00  thf('15', plain,
% 0.78/1.00      ((m1_subset_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)) @ 
% 0.78/1.00        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_D))))),
% 0.78/1.00      inference('sup-', [status(thm)], ['13', '14'])).
% 0.78/1.00  thf(t4_subset, axiom,
% 0.78/1.00    (![A:$i,B:$i,C:$i]:
% 0.78/1.00     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.78/1.00       ( m1_subset_1 @ A @ C ) ))).
% 0.78/1.00  thf('16', plain,
% 0.78/1.00      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.78/1.00         (~ (r2_hidden @ X20 @ X21)
% 0.78/1.00          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 0.78/1.00          | (m1_subset_1 @ X20 @ X22))),
% 0.78/1.00      inference('cnf', [status(esa)], [t4_subset])).
% 0.78/1.00  thf('17', plain,
% 0.78/1.00      (![X0 : $i]:
% 0.78/1.00         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_D)))
% 0.78/1.00          | ~ (r2_hidden @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 0.78/1.00      inference('sup-', [status(thm)], ['15', '16'])).
% 0.78/1.00  thf('18', plain,
% 0.78/1.00      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_D)))),
% 0.78/1.00      inference('sup-', [status(thm)], ['6', '17'])).
% 0.78/1.00  thf('19', plain, ($false), inference('demod', [status(thm)], ['0', '18'])).
% 0.78/1.00  
% 0.78/1.00  % SZS output end Refutation
% 0.78/1.00  
% 0.78/1.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
