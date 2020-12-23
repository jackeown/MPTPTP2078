%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lawNkPz57W

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:33 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   64 (  78 expanded)
%              Number of leaves         :   25 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :  370 ( 461 expanded)
%              Number of equality atoms :   30 (  41 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

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

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('2',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('3',plain,(
    ! [X6: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('4',plain,(
    ! [X18: $i] :
      ( ( k6_partfun1 @ X18 )
      = ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('5',plain,(
    ! [X6: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X6 ) )
      = X6 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X9 @ ( k2_relat_1 @ X10 ) )
      | ( ( k9_relat_1 @ X10 @ ( k10_relat_1 @ X10 @ X9 ) )
        = X9 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X7: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('9',plain,(
    ! [X18: $i] :
      ( ( k6_partfun1 @ X18 )
      = ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('10',plain,(
    ! [X7: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X7 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X8: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('12',plain,(
    ! [X18: $i] :
      ( ( k6_partfun1 @ X18 )
      = ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('13',plain,(
    ! [X8: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X8 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['7','10','13'])).

thf('15',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('16',plain,(
    ! [X18: $i] :
      ( ( k6_partfun1 @ X18 )
      = ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('17',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X5 ) )
      = X5 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X3 @ X4 ) @ ( k1_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X7: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X7 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t162_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B )
        = B ) ) )).

thf('24',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X12 ) @ X11 )
        = X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t162_funct_1])).

thf('25',plain,(
    ! [X18: $i] :
      ( ( k6_partfun1 @ X18 )
      = ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('26',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k9_relat_1 @ ( k6_partfun1 @ X12 ) @ X11 )
        = X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
      = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 )
        = X1 ) ) ),
    inference(demod,[status(thm)],['14','27'])).

thf('29',plain,
    ( ( k10_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['2','28'])).

thf('30',plain,(
    ( k8_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('31',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('32',plain,(
    ! [X18: $i] :
      ( ( k6_partfun1 @ X18 )
      = ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('33',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('34',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( ( k8_relset_1 @ X14 @ X15 @ X13 @ X16 )
        = ( k10_relat_1 @ X13 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ( k10_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(demod,[status(thm)],['30','35'])).

thf('37',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['29','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lawNkPz57W
% 0.17/0.37  % Computer   : n024.cluster.edu
% 0.17/0.37  % Model      : x86_64 x86_64
% 0.17/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.37  % Memory     : 8042.1875MB
% 0.17/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.37  % CPULimit   : 60
% 0.17/0.37  % DateTime   : Tue Dec  1 09:55:06 EST 2020
% 0.17/0.37  % CPUTime    : 
% 0.17/0.37  % Running portfolio for 600 s
% 0.17/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.37  % Number of cores: 8
% 0.17/0.37  % Python version: Python 3.6.8
% 0.17/0.37  % Running in FO mode
% 0.23/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.50  % Solved by: fo/fo7.sh
% 0.23/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.50  % done 30 iterations in 0.020s
% 0.23/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.50  % SZS output start Refutation
% 0.23/0.50  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.23/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.50  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.23/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.50  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.23/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.23/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.23/0.50  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.23/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.23/0.50  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.23/0.50  thf(t171_funct_2, conjecture,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.50       ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ))).
% 0.23/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.50    (~( ![A:$i,B:$i]:
% 0.23/0.50        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.50          ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ) )),
% 0.23/0.50    inference('cnf.neg', [status(esa)], [t171_funct_2])).
% 0.23/0.50  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf(t3_subset, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.23/0.50  thf('1', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]:
% 0.23/0.50         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.23/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.23/0.50  thf('2', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.23/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.23/0.50  thf(t71_relat_1, axiom,
% 0.23/0.50    (![A:$i]:
% 0.23/0.50     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.23/0.50       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.23/0.50  thf('3', plain, (![X6 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X6)) = (X6))),
% 0.23/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.23/0.50  thf(redefinition_k6_partfun1, axiom,
% 0.23/0.50    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.23/0.50  thf('4', plain, (![X18 : $i]: ((k6_partfun1 @ X18) = (k6_relat_1 @ X18))),
% 0.23/0.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.23/0.50  thf('5', plain, (![X6 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X6)) = (X6))),
% 0.23/0.50      inference('demod', [status(thm)], ['3', '4'])).
% 0.23/0.50  thf(t147_funct_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.23/0.50       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.23/0.50         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.23/0.50  thf('6', plain,
% 0.23/0.50      (![X9 : $i, X10 : $i]:
% 0.23/0.50         (~ (r1_tarski @ X9 @ (k2_relat_1 @ X10))
% 0.23/0.50          | ((k9_relat_1 @ X10 @ (k10_relat_1 @ X10 @ X9)) = (X9))
% 0.23/0.50          | ~ (v1_funct_1 @ X10)
% 0.23/0.50          | ~ (v1_relat_1 @ X10))),
% 0.23/0.50      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.23/0.50  thf('7', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]:
% 0.23/0.50         (~ (r1_tarski @ X1 @ X0)
% 0.23/0.50          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 0.23/0.50          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 0.23/0.50          | ((k9_relat_1 @ (k6_partfun1 @ X0) @ 
% 0.23/0.50              (k10_relat_1 @ (k6_partfun1 @ X0) @ X1)) = (X1)))),
% 0.23/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.23/0.50  thf(fc3_funct_1, axiom,
% 0.23/0.50    (![A:$i]:
% 0.23/0.50     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.23/0.50       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.23/0.50  thf('8', plain, (![X7 : $i]: (v1_relat_1 @ (k6_relat_1 @ X7))),
% 0.23/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.23/0.50  thf('9', plain, (![X18 : $i]: ((k6_partfun1 @ X18) = (k6_relat_1 @ X18))),
% 0.23/0.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.23/0.50  thf('10', plain, (![X7 : $i]: (v1_relat_1 @ (k6_partfun1 @ X7))),
% 0.23/0.50      inference('demod', [status(thm)], ['8', '9'])).
% 0.23/0.50  thf('11', plain, (![X8 : $i]: (v1_funct_1 @ (k6_relat_1 @ X8))),
% 0.23/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.23/0.50  thf('12', plain, (![X18 : $i]: ((k6_partfun1 @ X18) = (k6_relat_1 @ X18))),
% 0.23/0.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.23/0.50  thf('13', plain, (![X8 : $i]: (v1_funct_1 @ (k6_partfun1 @ X8))),
% 0.23/0.50      inference('demod', [status(thm)], ['11', '12'])).
% 0.23/0.50  thf('14', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]:
% 0.23/0.50         (~ (r1_tarski @ X1 @ X0)
% 0.23/0.50          | ((k9_relat_1 @ (k6_partfun1 @ X0) @ 
% 0.23/0.50              (k10_relat_1 @ (k6_partfun1 @ X0) @ X1)) = (X1)))),
% 0.23/0.50      inference('demod', [status(thm)], ['7', '10', '13'])).
% 0.23/0.50  thf('15', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 0.23/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.23/0.50  thf('16', plain, (![X18 : $i]: ((k6_partfun1 @ X18) = (k6_relat_1 @ X18))),
% 0.23/0.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.23/0.50  thf('17', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X5)) = (X5))),
% 0.23/0.50      inference('demod', [status(thm)], ['15', '16'])).
% 0.23/0.50  thf(t167_relat_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( v1_relat_1 @ B ) =>
% 0.23/0.50       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.23/0.50  thf('18', plain,
% 0.23/0.50      (![X3 : $i, X4 : $i]:
% 0.23/0.50         ((r1_tarski @ (k10_relat_1 @ X3 @ X4) @ (k1_relat_1 @ X3))
% 0.23/0.50          | ~ (v1_relat_1 @ X3))),
% 0.23/0.50      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.23/0.50  thf('19', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]:
% 0.23/0.50         ((r1_tarski @ (k10_relat_1 @ (k6_partfun1 @ X0) @ X1) @ X0)
% 0.23/0.50          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 0.23/0.50      inference('sup+', [status(thm)], ['17', '18'])).
% 0.23/0.50  thf('20', plain, (![X7 : $i]: (v1_relat_1 @ (k6_partfun1 @ X7))),
% 0.23/0.50      inference('demod', [status(thm)], ['8', '9'])).
% 0.23/0.50  thf('21', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]:
% 0.23/0.50         (r1_tarski @ (k10_relat_1 @ (k6_partfun1 @ X0) @ X1) @ X0)),
% 0.23/0.50      inference('demod', [status(thm)], ['19', '20'])).
% 0.23/0.50  thf('22', plain,
% 0.23/0.50      (![X0 : $i, X2 : $i]:
% 0.23/0.50         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.23/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.23/0.50  thf('23', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]:
% 0.23/0.50         (m1_subset_1 @ (k10_relat_1 @ (k6_partfun1 @ X0) @ X1) @ 
% 0.23/0.50          (k1_zfmisc_1 @ X0))),
% 0.23/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.23/0.50  thf(t162_funct_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.50       ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ))).
% 0.23/0.50  thf('24', plain,
% 0.23/0.50      (![X11 : $i, X12 : $i]:
% 0.23/0.50         (((k9_relat_1 @ (k6_relat_1 @ X12) @ X11) = (X11))
% 0.23/0.50          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.23/0.50      inference('cnf', [status(esa)], [t162_funct_1])).
% 0.23/0.50  thf('25', plain, (![X18 : $i]: ((k6_partfun1 @ X18) = (k6_relat_1 @ X18))),
% 0.23/0.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.23/0.50  thf('26', plain,
% 0.23/0.50      (![X11 : $i, X12 : $i]:
% 0.23/0.50         (((k9_relat_1 @ (k6_partfun1 @ X12) @ X11) = (X11))
% 0.23/0.50          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.23/0.50      inference('demod', [status(thm)], ['24', '25'])).
% 0.23/0.50  thf('27', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]:
% 0.23/0.50         ((k9_relat_1 @ (k6_partfun1 @ X0) @ 
% 0.23/0.50           (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 0.23/0.50           = (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.23/0.50      inference('sup-', [status(thm)], ['23', '26'])).
% 0.23/0.50  thf('28', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]:
% 0.23/0.50         (~ (r1_tarski @ X1 @ X0)
% 0.23/0.50          | ((k10_relat_1 @ (k6_partfun1 @ X0) @ X1) = (X1)))),
% 0.23/0.50      inference('demod', [status(thm)], ['14', '27'])).
% 0.23/0.50  thf('29', plain, (((k10_relat_1 @ (k6_partfun1 @ sk_A) @ sk_B) = (sk_B))),
% 0.23/0.50      inference('sup-', [status(thm)], ['2', '28'])).
% 0.23/0.50  thf('30', plain,
% 0.23/0.50      (((k8_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ sk_B) != (sk_B))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf(t29_relset_1, axiom,
% 0.23/0.50    (![A:$i]:
% 0.23/0.50     ( m1_subset_1 @
% 0.23/0.50       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.23/0.50  thf('31', plain,
% 0.23/0.50      (![X17 : $i]:
% 0.23/0.50         (m1_subset_1 @ (k6_relat_1 @ X17) @ 
% 0.23/0.50          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))),
% 0.23/0.50      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.23/0.50  thf('32', plain, (![X18 : $i]: ((k6_partfun1 @ X18) = (k6_relat_1 @ X18))),
% 0.23/0.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.23/0.50  thf('33', plain,
% 0.23/0.50      (![X17 : $i]:
% 0.23/0.50         (m1_subset_1 @ (k6_partfun1 @ X17) @ 
% 0.23/0.50          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))),
% 0.23/0.50      inference('demod', [status(thm)], ['31', '32'])).
% 0.23/0.50  thf(redefinition_k8_relset_1, axiom,
% 0.23/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.50       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.23/0.50  thf('34', plain,
% 0.23/0.50      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.23/0.50         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.23/0.50          | ((k8_relset_1 @ X14 @ X15 @ X13 @ X16) = (k10_relat_1 @ X13 @ X16)))),
% 0.23/0.50      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.23/0.50  thf('35', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]:
% 0.23/0.50         ((k8_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 0.23/0.50           = (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.23/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.23/0.50  thf('36', plain, (((k10_relat_1 @ (k6_partfun1 @ sk_A) @ sk_B) != (sk_B))),
% 0.23/0.50      inference('demod', [status(thm)], ['30', '35'])).
% 0.23/0.50  thf('37', plain, ($false),
% 0.23/0.50      inference('simplify_reflect-', [status(thm)], ['29', '36'])).
% 0.23/0.50  
% 0.23/0.50  % SZS output end Refutation
% 0.23/0.50  
% 0.23/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
