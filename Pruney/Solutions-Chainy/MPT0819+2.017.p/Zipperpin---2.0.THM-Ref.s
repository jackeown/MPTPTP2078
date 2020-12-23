%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GXXtzzDR6d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:47 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   38 (  44 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :  224 ( 332 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ( r2_hidden @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X6: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('5',plain,(
    r2_hidden @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t119_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D ) )
     => ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t119_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ X1 ) @ ( k2_zfmisc_1 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_C ) @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(t79_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X4 ) @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('12',plain,(
    r1_tarski @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    m1_subset_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('15',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( m1_subset_1 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['5','16'])).

thf('18',plain,(
    $false ),
    inference(demod,[status(thm)],['0','17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GXXtzzDR6d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:15:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.34/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.34/0.53  % Solved by: fo/fo7.sh
% 0.34/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.53  % done 136 iterations in 0.058s
% 0.34/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.34/0.53  % SZS output start Refutation
% 0.34/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.34/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.34/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.34/0.53  thf(sk_E_type, type, sk_E: $i).
% 0.34/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.34/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.34/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.34/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.34/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.34/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.34/0.53  thf(t17_relset_1, conjecture,
% 0.34/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.34/0.53     ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.34/0.53       ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.34/0.53         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ D ) ) ) ) ))).
% 0.34/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.53    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.34/0.53        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.34/0.53          ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.34/0.53            ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ D ) ) ) ) ) )),
% 0.34/0.53    inference('cnf.neg', [status(esa)], [t17_relset_1])).
% 0.34/0.53  thf('0', plain,
% 0.34/0.53      (~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_D)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('1', plain,
% 0.34/0.53      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(t2_subset, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( m1_subset_1 @ A @ B ) =>
% 0.34/0.53       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.34/0.53  thf('2', plain,
% 0.34/0.53      (![X7 : $i, X8 : $i]:
% 0.34/0.53         ((r2_hidden @ X7 @ X8)
% 0.34/0.53          | (v1_xboole_0 @ X8)
% 0.34/0.53          | ~ (m1_subset_1 @ X7 @ X8))),
% 0.34/0.53      inference('cnf', [status(esa)], [t2_subset])).
% 0.34/0.53  thf('3', plain,
% 0.34/0.53      (((v1_xboole_0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))
% 0.34/0.53        | (r2_hidden @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.34/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.34/0.53  thf(fc1_subset_1, axiom,
% 0.34/0.53    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.34/0.53  thf('4', plain, (![X6 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.34/0.53      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.34/0.53  thf('5', plain,
% 0.34/0.53      ((r2_hidden @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.34/0.53      inference('clc', [status(thm)], ['3', '4'])).
% 0.34/0.53  thf('6', plain, ((r1_tarski @ sk_C @ sk_D)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('7', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(t119_zfmisc_1, axiom,
% 0.34/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.34/0.53     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.34/0.53       ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.34/0.53  thf('8', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.34/0.53         (~ (r1_tarski @ X0 @ X1)
% 0.34/0.53          | ~ (r1_tarski @ X2 @ X3)
% 0.34/0.53          | (r1_tarski @ (k2_zfmisc_1 @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 0.34/0.53      inference('cnf', [status(esa)], [t119_zfmisc_1])).
% 0.34/0.53  thf('9', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]:
% 0.34/0.53         ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ X1) @ (k2_zfmisc_1 @ sk_B @ X0))
% 0.34/0.53          | ~ (r1_tarski @ X1 @ X0))),
% 0.34/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.34/0.53  thf('10', plain,
% 0.34/0.53      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_C) @ (k2_zfmisc_1 @ sk_B @ sk_D))),
% 0.34/0.53      inference('sup-', [status(thm)], ['6', '9'])).
% 0.34/0.53  thf(t79_zfmisc_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( r1_tarski @ A @ B ) =>
% 0.34/0.53       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.34/0.53  thf('11', plain,
% 0.34/0.53      (![X4 : $i, X5 : $i]:
% 0.34/0.53         ((r1_tarski @ (k1_zfmisc_1 @ X4) @ (k1_zfmisc_1 @ X5))
% 0.34/0.53          | ~ (r1_tarski @ X4 @ X5))),
% 0.34/0.53      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 0.34/0.53  thf('12', plain,
% 0.34/0.53      ((r1_tarski @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)) @ 
% 0.34/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_D)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.34/0.53  thf(t3_subset, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.34/0.53  thf('13', plain,
% 0.34/0.53      (![X9 : $i, X11 : $i]:
% 0.34/0.53         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 0.34/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.34/0.53  thf('14', plain,
% 0.34/0.53      ((m1_subset_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)) @ 
% 0.34/0.53        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_D))))),
% 0.34/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.34/0.53  thf(t4_subset, axiom,
% 0.34/0.53    (![A:$i,B:$i,C:$i]:
% 0.34/0.53     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.34/0.53       ( m1_subset_1 @ A @ C ) ))).
% 0.34/0.53  thf('15', plain,
% 0.34/0.53      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.34/0.53         (~ (r2_hidden @ X12 @ X13)
% 0.34/0.53          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.34/0.53          | (m1_subset_1 @ X12 @ X14))),
% 0.34/0.53      inference('cnf', [status(esa)], [t4_subset])).
% 0.34/0.53  thf('16', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_D)))
% 0.34/0.53          | ~ (r2_hidden @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.34/0.53      inference('sup-', [status(thm)], ['14', '15'])).
% 0.34/0.53  thf('17', plain,
% 0.34/0.53      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_D)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['5', '16'])).
% 0.34/0.53  thf('18', plain, ($false), inference('demod', [status(thm)], ['0', '17'])).
% 0.34/0.53  
% 0.34/0.53  % SZS output end Refutation
% 0.34/0.53  
% 0.37/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
