%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DbKCi8uwih

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   70 (  92 expanded)
%              Number of leaves         :   28 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :  407 ( 573 expanded)
%              Number of equality atoms :   27 (  45 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t171_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t171_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t162_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B )
        = B ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X17 ) @ X16 )
        = X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t162_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X23: $i] :
      ( ( k6_partfun1 @ X23 )
      = ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k9_relat_1 @ ( k6_partfun1 @ X17 ) @ X16 )
        = X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k9_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t152_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( r1_tarski @ ( k10_relat_1 @ X14 @ ( k9_relat_1 @ X14 @ X15 ) ) @ X15 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf('6',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_B ) @ sk_B )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X8: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('8',plain,(
    ! [X23: $i] :
      ( ( k6_partfun1 @ X23 )
      = ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('9',plain,(
    ! [X8: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X8 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X9: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('11',plain,(
    ! [X23: $i] :
      ( ( k6_partfun1 @ X23 )
      = ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('12',plain,(
    ! [X9: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X9 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('13',plain,(
    ! [X11: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('14',plain,(
    ! [X23: $i] :
      ( ( k6_partfun1 @ X23 )
      = ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('15',plain,(
    ! [X11: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X11 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ ( k10_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['6','9','12','15'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k10_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_B ) )
    | ( sk_B
      = ( k10_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('21',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('22',plain,(
    ! [X6: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('23',plain,(
    ! [X23: $i] :
      ( ( k6_partfun1 @ X23 )
      = ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('24',plain,(
    ! [X6: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X6 ) )
      = X6 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('25',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X12 @ ( k1_relat_1 @ X13 ) )
      | ( r1_tarski @ X12 @ ( k10_relat_1 @ X13 @ ( k9_relat_1 @ X13 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( r1_tarski @ X1 @ ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X8: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X8 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ X1 @ ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    r1_tarski @ sk_B @ ( k10_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k9_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','28'])).

thf('30',plain,
    ( ( k9_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['0','3'])).

thf('31',plain,(
    r1_tarski @ sk_B @ ( k10_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( sk_B
    = ( k10_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['18','31'])).

thf('33',plain,(
    ( k8_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('34',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('35',plain,(
    ! [X23: $i] :
      ( ( k6_partfun1 @ X23 )
      = ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('36',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('37',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( ( k8_relset_1 @ X19 @ X20 @ X18 @ X21 )
        = ( k10_relat_1 @ X18 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ( k10_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(demod,[status(thm)],['33','38'])).

thf('40',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['32','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DbKCi8uwih
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:51:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 58 iterations in 0.033s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.50  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.50  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.50  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.50  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.50  thf(t171_funct_2, conjecture,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.50       ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i]:
% 0.21/0.50        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.50          ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t171_funct_2])).
% 0.21/0.50  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t162_funct_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.50       ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ))).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (![X16 : $i, X17 : $i]:
% 0.21/0.50         (((k9_relat_1 @ (k6_relat_1 @ X17) @ X16) = (X16))
% 0.21/0.50          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t162_funct_1])).
% 0.21/0.50  thf(redefinition_k6_partfun1, axiom,
% 0.21/0.50    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.21/0.50  thf('2', plain, (![X23 : $i]: ((k6_partfun1 @ X23) = (k6_relat_1 @ X23))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X16 : $i, X17 : $i]:
% 0.21/0.50         (((k9_relat_1 @ (k6_partfun1 @ X17) @ X16) = (X16))
% 0.21/0.50          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.21/0.50      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.50  thf('4', plain, (((k9_relat_1 @ (k6_partfun1 @ sk_A) @ sk_B) = (sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['0', '3'])).
% 0.21/0.50  thf(t152_funct_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.50       ( ( v2_funct_1 @ B ) =>
% 0.21/0.50         ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ))).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X14 : $i, X15 : $i]:
% 0.21/0.50         (~ (v2_funct_1 @ X14)
% 0.21/0.50          | (r1_tarski @ (k10_relat_1 @ X14 @ (k9_relat_1 @ X14 @ X15)) @ X15)
% 0.21/0.50          | ~ (v1_funct_1 @ X14)
% 0.21/0.50          | ~ (v1_relat_1 @ X14))),
% 0.21/0.50      inference('cnf', [status(esa)], [t152_funct_1])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (((r1_tarski @ (k10_relat_1 @ (k6_partfun1 @ sk_A) @ sk_B) @ sk_B)
% 0.21/0.50        | ~ (v1_relat_1 @ (k6_partfun1 @ sk_A))
% 0.21/0.50        | ~ (v1_funct_1 @ (k6_partfun1 @ sk_A))
% 0.21/0.50        | ~ (v2_funct_1 @ (k6_partfun1 @ sk_A)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['4', '5'])).
% 0.21/0.50  thf(fc3_funct_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.21/0.50       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.21/0.50  thf('7', plain, (![X8 : $i]: (v1_relat_1 @ (k6_relat_1 @ X8))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.50  thf('8', plain, (![X23 : $i]: ((k6_partfun1 @ X23) = (k6_relat_1 @ X23))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.50  thf('9', plain, (![X8 : $i]: (v1_relat_1 @ (k6_partfun1 @ X8))),
% 0.21/0.50      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.50  thf('10', plain, (![X9 : $i]: (v1_funct_1 @ (k6_relat_1 @ X9))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.50  thf('11', plain, (![X23 : $i]: ((k6_partfun1 @ X23) = (k6_relat_1 @ X23))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.50  thf('12', plain, (![X9 : $i]: (v1_funct_1 @ (k6_partfun1 @ X9))),
% 0.21/0.50      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf(fc4_funct_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.21/0.50       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.21/0.50  thf('13', plain, (![X11 : $i]: (v2_funct_1 @ (k6_relat_1 @ X11))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.21/0.50  thf('14', plain, (![X23 : $i]: ((k6_partfun1 @ X23) = (k6_relat_1 @ X23))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.50  thf('15', plain, (![X11 : $i]: (v2_funct_1 @ (k6_partfun1 @ X11))),
% 0.21/0.50      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      ((r1_tarski @ (k10_relat_1 @ (k6_partfun1 @ sk_A) @ sk_B) @ sk_B)),
% 0.21/0.50      inference('demod', [status(thm)], ['6', '9', '12', '15'])).
% 0.21/0.50  thf(d10_xboole_0, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (![X0 : $i, X2 : $i]:
% 0.21/0.50         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      ((~ (r1_tarski @ sk_B @ (k10_relat_1 @ (k6_partfun1 @ sk_A) @ sk_B))
% 0.21/0.50        | ((sk_B) = (k10_relat_1 @ (k6_partfun1 @ sk_A) @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.50  thf('19', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t3_subset, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X3 : $i, X4 : $i]:
% 0.21/0.50         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.50  thf('21', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.21/0.50      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.50  thf(t71_relat_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.21/0.50       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.50  thf('22', plain, (![X6 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X6)) = (X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.50  thf('23', plain, (![X23 : $i]: ((k6_partfun1 @ X23) = (k6_relat_1 @ X23))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.50  thf('24', plain, (![X6 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X6)) = (X6))),
% 0.21/0.50      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.50  thf(t146_funct_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ B ) =>
% 0.21/0.50       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.50         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      (![X12 : $i, X13 : $i]:
% 0.21/0.50         (~ (r1_tarski @ X12 @ (k1_relat_1 @ X13))
% 0.21/0.50          | (r1_tarski @ X12 @ (k10_relat_1 @ X13 @ (k9_relat_1 @ X13 @ X12)))
% 0.21/0.50          | ~ (v1_relat_1 @ X13))),
% 0.21/0.50      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (r1_tarski @ X1 @ X0)
% 0.21/0.50          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 0.21/0.50          | (r1_tarski @ X1 @ 
% 0.21/0.50             (k10_relat_1 @ (k6_partfun1 @ X0) @ 
% 0.21/0.50              (k9_relat_1 @ (k6_partfun1 @ X0) @ X1))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.50  thf('27', plain, (![X8 : $i]: (v1_relat_1 @ (k6_partfun1 @ X8))),
% 0.21/0.50      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (r1_tarski @ X1 @ X0)
% 0.21/0.50          | (r1_tarski @ X1 @ 
% 0.21/0.50             (k10_relat_1 @ (k6_partfun1 @ X0) @ 
% 0.21/0.50              (k9_relat_1 @ (k6_partfun1 @ X0) @ X1))))),
% 0.21/0.50      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      ((r1_tarski @ sk_B @ 
% 0.21/0.50        (k10_relat_1 @ (k6_partfun1 @ sk_A) @ 
% 0.21/0.50         (k9_relat_1 @ (k6_partfun1 @ sk_A) @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['21', '28'])).
% 0.21/0.50  thf('30', plain, (((k9_relat_1 @ (k6_partfun1 @ sk_A) @ sk_B) = (sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['0', '3'])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      ((r1_tarski @ sk_B @ (k10_relat_1 @ (k6_partfun1 @ sk_A) @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.50  thf('32', plain, (((sk_B) = (k10_relat_1 @ (k6_partfun1 @ sk_A) @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['18', '31'])).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      (((k8_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ sk_B) != (sk_B))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t29_relset_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( m1_subset_1 @
% 0.21/0.50       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      (![X22 : $i]:
% 0.21/0.50         (m1_subset_1 @ (k6_relat_1 @ X22) @ 
% 0.21/0.50          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.21/0.50  thf('35', plain, (![X23 : $i]: ((k6_partfun1 @ X23) = (k6_relat_1 @ X23))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      (![X22 : $i]:
% 0.21/0.50         (m1_subset_1 @ (k6_partfun1 @ X22) @ 
% 0.21/0.50          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 0.21/0.50      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.50  thf(redefinition_k8_relset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.21/0.50          | ((k8_relset_1 @ X19 @ X20 @ X18 @ X21) = (k10_relat_1 @ X18 @ X21)))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((k8_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 0.21/0.50           = (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.50  thf('39', plain, (((k10_relat_1 @ (k6_partfun1 @ sk_A) @ sk_B) != (sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['33', '38'])).
% 0.21/0.50  thf('40', plain, ($false),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['32', '39'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
