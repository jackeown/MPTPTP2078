%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.U25Zfoxqly

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:57 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   21 (  23 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :  101 ( 131 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t47_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r1_tarski @ ( k8_relset_1 @ A @ B @ D @ C ) @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( r1_tarski @ ( k8_relset_1 @ A @ B @ D @ C ) @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t47_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ( m1_subset_1 @ ( k8_relset_1 @ X4 @ X5 @ X3 @ X6 ) @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D @ X0 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    $false ),
    inference(demod,[status(thm)],['0','5'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.U25Zfoxqly
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:09:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 9 iterations in 0.010s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.46  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.46  thf(t47_funct_2, conjecture,
% 0.20/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.46     ( ( ( v1_funct_1 @ D ) & 
% 0.20/0.46         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.46       ( r1_tarski @ ( k8_relset_1 @ A @ B @ D @ C ) @ A ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.46        ( ( ( v1_funct_1 @ D ) & 
% 0.20/0.46            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.46          ( r1_tarski @ ( k8_relset_1 @ A @ B @ D @ C ) @ A ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t47_funct_2])).
% 0.20/0.46  thf('0', plain,
% 0.20/0.46      (~ (r1_tarski @ (k8_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(dt_k8_relset_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.46       ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5)))
% 0.20/0.46          | (m1_subset_1 @ (k8_relset_1 @ X4 @ X5 @ X3 @ X6) @ 
% 0.20/0.46             (k1_zfmisc_1 @ X4)))),
% 0.20/0.46      inference('cnf', [status(esa)], [dt_k8_relset_1])).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (m1_subset_1 @ (k8_relset_1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 0.20/0.46          (k1_zfmisc_1 @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.46  thf(t3_subset, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (![X0 : $i]: (r1_tarski @ (k8_relset_1 @ sk_A @ sk_B @ sk_D @ X0) @ sk_A)),
% 0.20/0.46      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.46  thf('6', plain, ($false), inference('demod', [status(thm)], ['0', '5'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
