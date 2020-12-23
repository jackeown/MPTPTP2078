%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.S9mg0DgZ9M

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:33 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   60 (  70 expanded)
%              Number of leaves         :   26 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :  326 ( 405 expanded)
%              Number of equality atoms :   28 (  37 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ( k8_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('1',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X18: $i] :
      ( ( k6_partfun1 @ X18 )
      = ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( ( k8_relset_1 @ X14 @ X15 @ X13 @ X16 )
        = ( k10_relat_1 @ X13 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('9',plain,(
    ! [X3: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X3 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('10',plain,(
    ! [X18: $i] :
      ( ( k6_partfun1 @ X18 )
      = ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('11',plain,(
    ! [X3: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X3 ) )
      = X3 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t164_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X11 @ ( k1_relat_1 @ X12 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ( ( k10_relat_1 @ X12 @ ( k9_relat_1 @ X12 @ X11 ) )
        = X11 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t164_funct_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
        = X1 )
      | ~ ( v2_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('14',plain,(
    ! [X5: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('15',plain,(
    ! [X18: $i] :
      ( ( k6_partfun1 @ X18 )
      = ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('16',plain,(
    ! [X5: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X5 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X6: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('18',plain,(
    ! [X18: $i] :
      ( ( k6_partfun1 @ X18 )
      = ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('19',plain,(
    ! [X6: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X6 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('20',plain,(
    ! [X8: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('21',plain,(
    ! [X18: $i] :
      ( ( k6_partfun1 @ X18 )
      = ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('22',plain,(
    ! [X8: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X8 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['13','16','19','22'])).

thf('24',plain,
    ( ( k10_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k9_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['8','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t162_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B )
        = B ) ) )).

thf('26',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X10 ) @ X9 )
        = X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t162_funct_1])).

thf('27',plain,(
    ! [X18: $i] :
      ( ( k6_partfun1 @ X18 )
      = ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('28',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k9_relat_1 @ ( k6_partfun1 @ X10 ) @ X9 )
        = X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k9_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,
    ( ( k10_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['24','29'])).

thf('31',plain,(
    sk_B != sk_B ),
    inference(demod,[status(thm)],['0','5','30'])).

thf('32',plain,(
    $false ),
    inference(simplify,[status(thm)],['31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.S9mg0DgZ9M
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:52:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 26 iterations in 0.014s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.46  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.46  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.46  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.20/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.46  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.46  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.46  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.46  thf(t171_funct_2, conjecture,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.46       ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i,B:$i]:
% 0.20/0.46        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.46          ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t171_funct_2])).
% 0.20/0.46  thf('0', plain,
% 0.20/0.46      (((k8_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ sk_B) != (sk_B))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(t29_relset_1, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( m1_subset_1 @
% 0.20/0.46       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      (![X17 : $i]:
% 0.20/0.46         (m1_subset_1 @ (k6_relat_1 @ X17) @ 
% 0.20/0.46          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.20/0.46  thf(redefinition_k6_partfun1, axiom,
% 0.20/0.46    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.20/0.46  thf('2', plain, (![X18 : $i]: ((k6_partfun1 @ X18) = (k6_relat_1 @ X18))),
% 0.20/0.46      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (![X17 : $i]:
% 0.20/0.46         (m1_subset_1 @ (k6_partfun1 @ X17) @ 
% 0.20/0.46          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))),
% 0.20/0.46      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.46  thf(redefinition_k8_relset_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.46       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.20/0.46          | ((k8_relset_1 @ X14 @ X15 @ X13 @ X16) = (k10_relat_1 @ X13 @ X16)))),
% 0.20/0.46      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((k8_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 0.20/0.46           = (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.20/0.46      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.46  thf('6', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(t3_subset, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.46  thf('8', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.20/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.46  thf(t71_relat_1, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.20/0.46       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.46  thf('9', plain, (![X3 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X3)) = (X3))),
% 0.20/0.46      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.46  thf('10', plain, (![X18 : $i]: ((k6_partfun1 @ X18) = (k6_relat_1 @ X18))),
% 0.20/0.46      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.46  thf('11', plain, (![X3 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X3)) = (X3))),
% 0.20/0.46      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.46  thf(t164_funct_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.46       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.20/0.46         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.20/0.46  thf('12', plain,
% 0.20/0.46      (![X11 : $i, X12 : $i]:
% 0.20/0.46         (~ (r1_tarski @ X11 @ (k1_relat_1 @ X12))
% 0.20/0.46          | ~ (v2_funct_1 @ X12)
% 0.20/0.46          | ((k10_relat_1 @ X12 @ (k9_relat_1 @ X12 @ X11)) = (X11))
% 0.20/0.46          | ~ (v1_funct_1 @ X12)
% 0.20/0.46          | ~ (v1_relat_1 @ X12))),
% 0.20/0.46      inference('cnf', [status(esa)], [t164_funct_1])).
% 0.20/0.46  thf('13', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         (~ (r1_tarski @ X1 @ X0)
% 0.20/0.46          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 0.20/0.46          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 0.20/0.46          | ((k10_relat_1 @ (k6_partfun1 @ X0) @ 
% 0.20/0.46              (k9_relat_1 @ (k6_partfun1 @ X0) @ X1)) = (X1))
% 0.20/0.46          | ~ (v2_funct_1 @ (k6_partfun1 @ X0)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.46  thf(fc3_funct_1, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.20/0.46       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.20/0.46  thf('14', plain, (![X5 : $i]: (v1_relat_1 @ (k6_relat_1 @ X5))),
% 0.20/0.46      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.46  thf('15', plain, (![X18 : $i]: ((k6_partfun1 @ X18) = (k6_relat_1 @ X18))),
% 0.20/0.46      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.46  thf('16', plain, (![X5 : $i]: (v1_relat_1 @ (k6_partfun1 @ X5))),
% 0.20/0.46      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.46  thf('17', plain, (![X6 : $i]: (v1_funct_1 @ (k6_relat_1 @ X6))),
% 0.20/0.46      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.46  thf('18', plain, (![X18 : $i]: ((k6_partfun1 @ X18) = (k6_relat_1 @ X18))),
% 0.20/0.46      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.46  thf('19', plain, (![X6 : $i]: (v1_funct_1 @ (k6_partfun1 @ X6))),
% 0.20/0.46      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.46  thf(fc4_funct_1, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.20/0.46       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.20/0.46  thf('20', plain, (![X8 : $i]: (v2_funct_1 @ (k6_relat_1 @ X8))),
% 0.20/0.46      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.20/0.46  thf('21', plain, (![X18 : $i]: ((k6_partfun1 @ X18) = (k6_relat_1 @ X18))),
% 0.20/0.46      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.46  thf('22', plain, (![X8 : $i]: (v2_funct_1 @ (k6_partfun1 @ X8))),
% 0.20/0.46      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.46  thf('23', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         (~ (r1_tarski @ X1 @ X0)
% 0.20/0.46          | ((k10_relat_1 @ (k6_partfun1 @ X0) @ 
% 0.20/0.46              (k9_relat_1 @ (k6_partfun1 @ X0) @ X1)) = (X1)))),
% 0.20/0.46      inference('demod', [status(thm)], ['13', '16', '19', '22'])).
% 0.20/0.46  thf('24', plain,
% 0.20/0.46      (((k10_relat_1 @ (k6_partfun1 @ sk_A) @ 
% 0.20/0.46         (k9_relat_1 @ (k6_partfun1 @ sk_A) @ sk_B)) = (sk_B))),
% 0.20/0.46      inference('sup-', [status(thm)], ['8', '23'])).
% 0.20/0.46  thf('25', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(t162_funct_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.46       ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ))).
% 0.20/0.46  thf('26', plain,
% 0.20/0.46      (![X9 : $i, X10 : $i]:
% 0.20/0.46         (((k9_relat_1 @ (k6_relat_1 @ X10) @ X9) = (X9))
% 0.20/0.46          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t162_funct_1])).
% 0.20/0.46  thf('27', plain, (![X18 : $i]: ((k6_partfun1 @ X18) = (k6_relat_1 @ X18))),
% 0.20/0.46      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.46  thf('28', plain,
% 0.20/0.46      (![X9 : $i, X10 : $i]:
% 0.20/0.46         (((k9_relat_1 @ (k6_partfun1 @ X10) @ X9) = (X9))
% 0.20/0.46          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.20/0.46      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.46  thf('29', plain, (((k9_relat_1 @ (k6_partfun1 @ sk_A) @ sk_B) = (sk_B))),
% 0.20/0.46      inference('sup-', [status(thm)], ['25', '28'])).
% 0.20/0.46  thf('30', plain, (((k10_relat_1 @ (k6_partfun1 @ sk_A) @ sk_B) = (sk_B))),
% 0.20/0.46      inference('demod', [status(thm)], ['24', '29'])).
% 0.20/0.46  thf('31', plain, (((sk_B) != (sk_B))),
% 0.20/0.46      inference('demod', [status(thm)], ['0', '5', '30'])).
% 0.20/0.46  thf('32', plain, ($false), inference('simplify', [status(thm)], ['31'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
