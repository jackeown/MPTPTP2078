%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Byg0qdul25

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 (  78 expanded)
%              Number of leaves         :   24 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :  329 ( 456 expanded)
%              Number of equality atoms :   30 (  49 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ( k8_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('1',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X16: $i] :
      ( ( k6_partfun1 @ X16 )
      = ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( ( k8_relset_1 @ X12 @ X13 @ X11 @ X14 )
        = ( k10_relat_1 @ X11 @ X14 ) ) ) ),
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
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('10',plain,(
    ! [X16: $i] :
      ( ( k6_partfun1 @ X16 )
      = ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('11',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X5 ) )
      = X5 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X7 ) @ X8 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X8 ) @ X7 )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('13',plain,(
    ! [X16: $i] :
      ( ( k6_partfun1 @ X16 )
      = ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('14',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X7 ) @ X8 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X8 ) @ X7 )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('16',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('17',plain,(
    ! [X16: $i] :
      ( ( k6_partfun1 @ X16 )
      = ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('18',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X9 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_B ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','19'])).

thf('21',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X5 ) )
      = X5 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('22',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X4 @ X3 ) )
        = ( k10_relat_1 @ X4 @ ( k1_relat_1 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X9 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) )
      = ( k10_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X5 ) )
      = X5 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('28',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X9 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('29',plain,
    ( sk_B
    = ( k10_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    sk_B != sk_B ),
    inference(demod,[status(thm)],['0','5','29'])).

thf('31',plain,(
    $false ),
    inference(simplify,[status(thm)],['30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Byg0qdul25
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:53:25 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 25 iterations in 0.015s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.21/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.47  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.47  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.47  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.47  thf(t171_funct_2, conjecture,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.47       ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i]:
% 0.21/0.47        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.47          ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t171_funct_2])).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      (((k8_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ sk_B) != (sk_B))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t29_relset_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( m1_subset_1 @
% 0.21/0.47       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X15 : $i]:
% 0.21/0.47         (m1_subset_1 @ (k6_relat_1 @ X15) @ 
% 0.21/0.47          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X15)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.21/0.47  thf(redefinition_k6_partfun1, axiom,
% 0.21/0.47    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.21/0.47  thf('2', plain, (![X16 : $i]: ((k6_partfun1 @ X16) = (k6_relat_1 @ X16))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X15 : $i]:
% 0.21/0.47         (m1_subset_1 @ (k6_partfun1 @ X15) @ 
% 0.21/0.47          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X15)))),
% 0.21/0.47      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf(redefinition_k8_relset_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.47       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.21/0.47          | ((k8_relset_1 @ X12 @ X13 @ X11 @ X14) = (k10_relat_1 @ X11 @ X14)))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((k8_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 0.21/0.47           = (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.47  thf('6', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t3_subset, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.47  thf('8', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.21/0.47      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.47  thf(t71_relat_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.21/0.47       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.47  thf('9', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 0.21/0.47      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.47  thf('10', plain, (![X16 : $i]: ((k6_partfun1 @ X16) = (k6_relat_1 @ X16))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.47  thf('11', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X5)) = (X5))),
% 0.21/0.47      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.47  thf(t77_relat_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ B ) =>
% 0.21/0.47       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.21/0.47         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X7 : $i, X8 : $i]:
% 0.21/0.47         (~ (r1_tarski @ (k1_relat_1 @ X7) @ X8)
% 0.21/0.47          | ((k5_relat_1 @ (k6_relat_1 @ X8) @ X7) = (X7))
% 0.21/0.47          | ~ (v1_relat_1 @ X7))),
% 0.21/0.47      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.21/0.47  thf('13', plain, (![X16 : $i]: ((k6_partfun1 @ X16) = (k6_relat_1 @ X16))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (![X7 : $i, X8 : $i]:
% 0.21/0.47         (~ (r1_tarski @ (k1_relat_1 @ X7) @ X8)
% 0.21/0.47          | ((k5_relat_1 @ (k6_partfun1 @ X8) @ X7) = (X7))
% 0.21/0.47          | ~ (v1_relat_1 @ X7))),
% 0.21/0.47      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.47          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 0.21/0.47          | ((k5_relat_1 @ (k6_partfun1 @ X1) @ (k6_partfun1 @ X0))
% 0.21/0.47              = (k6_partfun1 @ X0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['11', '14'])).
% 0.21/0.47  thf(fc3_funct_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.21/0.47       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.21/0.47  thf('16', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.21/0.47      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.47  thf('17', plain, (![X16 : $i]: ((k6_partfun1 @ X16) = (k6_relat_1 @ X16))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.47  thf('18', plain, (![X9 : $i]: (v1_relat_1 @ (k6_partfun1 @ X9))),
% 0.21/0.47      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.47          | ((k5_relat_1 @ (k6_partfun1 @ X1) @ (k6_partfun1 @ X0))
% 0.21/0.47              = (k6_partfun1 @ X0)))),
% 0.21/0.47      inference('demod', [status(thm)], ['15', '18'])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      (((k5_relat_1 @ (k6_partfun1 @ sk_A) @ (k6_partfun1 @ sk_B))
% 0.21/0.47         = (k6_partfun1 @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['8', '19'])).
% 0.21/0.47  thf('21', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X5)) = (X5))),
% 0.21/0.47      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.47  thf(t182_relat_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( v1_relat_1 @ B ) =>
% 0.21/0.47           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.21/0.47             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.21/0.47  thf('22', plain,
% 0.21/0.47      (![X3 : $i, X4 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X3)
% 0.21/0.47          | ((k1_relat_1 @ (k5_relat_1 @ X4 @ X3))
% 0.21/0.47              = (k10_relat_1 @ X4 @ (k1_relat_1 @ X3)))
% 0.21/0.47          | ~ (v1_relat_1 @ X4))),
% 0.21/0.47      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.21/0.47  thf('23', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0)))
% 0.21/0.47            = (k10_relat_1 @ X1 @ X0))
% 0.21/0.47          | ~ (v1_relat_1 @ X1)
% 0.21/0.47          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 0.21/0.47      inference('sup+', [status(thm)], ['21', '22'])).
% 0.21/0.47  thf('24', plain, (![X9 : $i]: (v1_relat_1 @ (k6_partfun1 @ X9))),
% 0.21/0.47      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.47  thf('25', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0)))
% 0.21/0.47            = (k10_relat_1 @ X1 @ X0))
% 0.21/0.47          | ~ (v1_relat_1 @ X1))),
% 0.21/0.47      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.47  thf('26', plain,
% 0.21/0.47      ((((k1_relat_1 @ (k6_partfun1 @ sk_B))
% 0.21/0.47          = (k10_relat_1 @ (k6_partfun1 @ sk_A) @ sk_B))
% 0.21/0.47        | ~ (v1_relat_1 @ (k6_partfun1 @ sk_A)))),
% 0.21/0.47      inference('sup+', [status(thm)], ['20', '25'])).
% 0.21/0.47  thf('27', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X5)) = (X5))),
% 0.21/0.47      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.47  thf('28', plain, (![X9 : $i]: (v1_relat_1 @ (k6_partfun1 @ X9))),
% 0.21/0.47      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.47  thf('29', plain, (((sk_B) = (k10_relat_1 @ (k6_partfun1 @ sk_A) @ sk_B))),
% 0.21/0.47      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.21/0.47  thf('30', plain, (((sk_B) != (sk_B))),
% 0.21/0.47      inference('demod', [status(thm)], ['0', '5', '29'])).
% 0.21/0.47  thf('31', plain, ($false), inference('simplify', [status(thm)], ['30'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
