%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CvCogbpjr1

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   31 (  33 expanded)
%              Number of leaves         :   18 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :  163 ( 201 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t44_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r1_tarski @ ( k7_relset_1 @ A @ B @ D @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( r1_tarski @ ( k7_relset_1 @ A @ B @ D @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t44_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X9 @ X10 @ X8 @ X11 ) @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_B ) )
      | ( r2_hidden @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('6',plain,(
    ! [X5: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( r1_tarski @ X3 @ X1 )
      | ( X2
       != ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('9',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X3 @ X1 )
      | ~ ( r2_hidden @ X3 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    $false ),
    inference(demod,[status(thm)],['0','10'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CvCogbpjr1
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:51:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.45  % Solved by: fo/fo7.sh
% 0.21/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.45  % done 23 iterations in 0.010s
% 0.21/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.45  % SZS output start Refutation
% 0.21/0.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.45  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.45  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.45  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.45  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.45  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.45  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.45  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.45  thf(t44_funct_2, conjecture,
% 0.21/0.45    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.45     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.45         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.45       ( r1_tarski @ ( k7_relset_1 @ A @ B @ D @ C ) @ B ) ))).
% 0.21/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.45    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.45        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.45            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.45          ( r1_tarski @ ( k7_relset_1 @ A @ B @ D @ C ) @ B ) ) )),
% 0.21/0.45    inference('cnf.neg', [status(esa)], [t44_funct_2])).
% 0.21/0.45  thf('0', plain,
% 0.21/0.45      (~ (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C_1) @ sk_B)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('1', plain,
% 0.21/0.45      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf(dt_k7_relset_1, axiom,
% 0.21/0.45    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.45       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.21/0.45  thf('2', plain,
% 0.21/0.45      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.45         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.21/0.45          | (m1_subset_1 @ (k7_relset_1 @ X9 @ X10 @ X8 @ X11) @ 
% 0.21/0.45             (k1_zfmisc_1 @ X10)))),
% 0.21/0.45      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.21/0.45  thf('3', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         (m1_subset_1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 0.21/0.45          (k1_zfmisc_1 @ sk_B))),
% 0.21/0.45      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.45  thf(t2_subset, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.45       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.45  thf('4', plain,
% 0.21/0.45      (![X6 : $i, X7 : $i]:
% 0.21/0.45         ((r2_hidden @ X6 @ X7)
% 0.21/0.45          | (v1_xboole_0 @ X7)
% 0.21/0.45          | ~ (m1_subset_1 @ X6 @ X7))),
% 0.21/0.45      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.45  thf('5', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         ((v1_xboole_0 @ (k1_zfmisc_1 @ sk_B))
% 0.21/0.45          | (r2_hidden @ (k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 0.21/0.45             (k1_zfmisc_1 @ sk_B)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.45  thf(fc1_subset_1, axiom,
% 0.21/0.45    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.45  thf('6', plain, (![X5 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 0.21/0.45      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.21/0.45  thf('7', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         (r2_hidden @ (k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 0.21/0.45          (k1_zfmisc_1 @ sk_B))),
% 0.21/0.45      inference('clc', [status(thm)], ['5', '6'])).
% 0.21/0.45  thf(d1_zfmisc_1, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.21/0.45       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.21/0.45  thf('8', plain,
% 0.21/0.45      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.45         (~ (r2_hidden @ X3 @ X2)
% 0.21/0.45          | (r1_tarski @ X3 @ X1)
% 0.21/0.45          | ((X2) != (k1_zfmisc_1 @ X1)))),
% 0.21/0.45      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.21/0.45  thf('9', plain,
% 0.21/0.45      (![X1 : $i, X3 : $i]:
% 0.21/0.45         ((r1_tarski @ X3 @ X1) | ~ (r2_hidden @ X3 @ (k1_zfmisc_1 @ X1)))),
% 0.21/0.45      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.45  thf('10', plain,
% 0.21/0.45      (![X0 : $i]: (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0) @ sk_B)),
% 0.21/0.45      inference('sup-', [status(thm)], ['7', '9'])).
% 0.21/0.45  thf('11', plain, ($false), inference('demod', [status(thm)], ['0', '10'])).
% 0.21/0.45  
% 0.21/0.45  % SZS output end Refutation
% 0.21/0.45  
% 0.21/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
