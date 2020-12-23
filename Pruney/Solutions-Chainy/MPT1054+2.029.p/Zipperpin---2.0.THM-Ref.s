%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0h0ydIKM6W

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 (  62 expanded)
%              Number of leaves         :   24 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :  296 ( 351 expanded)
%              Number of equality atoms :   27 (  34 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('1',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X14 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ( ( k8_relset_1 @ X10 @ X11 @ X9 @ X12 )
        = ( k10_relat_1 @ X9 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t67_funct_1,axiom,(
    ! [A: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('4',plain,(
    ! [X8: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ X8 ) )
      = ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X15: $i] :
      ( ( k6_partfun1 @ X15 )
      = ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('6',plain,(
    ! [X15: $i] :
      ( ( k6_partfun1 @ X15 )
      = ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('7',plain,(
    ! [X8: $i] :
      ( ( k2_funct_1 @ ( k6_partfun1 @ X8 ) )
      = ( k6_partfun1 @ X8 ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(t154_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k9_relat_1 @ B @ A )
          = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k9_relat_1 @ X4 @ X5 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X4 ) @ X5 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 )
        = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('11',plain,(
    ! [X15: $i] :
      ( ( k6_partfun1 @ X15 )
      = ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('12',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X1: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('14',plain,(
    ! [X15: $i] :
      ( ( k6_partfun1 @ X15 )
      = ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('15',plain,(
    ! [X1: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X1 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 )
        = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
      | ~ ( v2_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','12','15'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('17',plain,(
    ! [X3: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('18',plain,(
    ! [X15: $i] :
      ( ( k6_partfun1 @ X15 )
      = ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('19',plain,(
    ! [X3: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X3 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['3','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t162_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B )
        = B ) ) )).

thf('23',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X7 ) @ X6 )
        = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t162_funct_1])).

thf('24',plain,(
    ! [X15: $i] :
      ( ( k6_partfun1 @ X15 )
      = ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('25',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k9_relat_1 @ ( k6_partfun1 @ X7 ) @ X6 )
        = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k9_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    sk_B != sk_B ),
    inference(demod,[status(thm)],['0','21','26'])).

thf('28',plain,(
    $false ),
    inference(simplify,[status(thm)],['27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0h0ydIKM6W
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:26:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 19 iterations in 0.012s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.46  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.46  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.21/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.46  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.21/0.46  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.21/0.46  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.46  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.46  thf(t171_funct_2, conjecture,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.46       ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i,B:$i]:
% 0.21/0.46        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.46          ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t171_funct_2])).
% 0.21/0.46  thf('0', plain,
% 0.21/0.46      (((k8_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ sk_B) != (sk_B))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(dt_k6_partfun1, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( m1_subset_1 @
% 0.21/0.46         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.21/0.46       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.21/0.46  thf('1', plain,
% 0.21/0.46      (![X14 : $i]:
% 0.21/0.46         (m1_subset_1 @ (k6_partfun1 @ X14) @ 
% 0.21/0.46          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X14)))),
% 0.21/0.46      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.21/0.46  thf(redefinition_k8_relset_1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.46       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.46         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 0.21/0.46          | ((k8_relset_1 @ X10 @ X11 @ X9 @ X12) = (k10_relat_1 @ X9 @ X12)))),
% 0.21/0.46      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.21/0.46  thf('3', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         ((k8_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 0.21/0.46           = (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.21/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.46  thf(t67_funct_1, axiom,
% 0.21/0.46    (![A:$i]: ( ( k2_funct_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.21/0.46  thf('4', plain,
% 0.21/0.46      (![X8 : $i]: ((k2_funct_1 @ (k6_relat_1 @ X8)) = (k6_relat_1 @ X8))),
% 0.21/0.46      inference('cnf', [status(esa)], [t67_funct_1])).
% 0.21/0.46  thf(redefinition_k6_partfun1, axiom,
% 0.21/0.46    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.21/0.46  thf('5', plain, (![X15 : $i]: ((k6_partfun1 @ X15) = (k6_relat_1 @ X15))),
% 0.21/0.46      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.46  thf('6', plain, (![X15 : $i]: ((k6_partfun1 @ X15) = (k6_relat_1 @ X15))),
% 0.21/0.46      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      (![X8 : $i]: ((k2_funct_1 @ (k6_partfun1 @ X8)) = (k6_partfun1 @ X8))),
% 0.21/0.46      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.21/0.46  thf(t154_funct_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.46       ( ( v2_funct_1 @ B ) =>
% 0.21/0.46         ( ( k9_relat_1 @ B @ A ) = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.21/0.46  thf('8', plain,
% 0.21/0.46      (![X4 : $i, X5 : $i]:
% 0.21/0.46         (~ (v2_funct_1 @ X4)
% 0.21/0.46          | ((k9_relat_1 @ X4 @ X5) = (k10_relat_1 @ (k2_funct_1 @ X4) @ X5))
% 0.21/0.46          | ~ (v1_funct_1 @ X4)
% 0.21/0.46          | ~ (v1_relat_1 @ X4))),
% 0.21/0.46      inference('cnf', [status(esa)], [t154_funct_1])).
% 0.21/0.46  thf('9', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         (((k9_relat_1 @ (k6_partfun1 @ X0) @ X1)
% 0.21/0.46            = (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 0.21/0.46          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 0.21/0.46          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 0.21/0.46          | ~ (v2_funct_1 @ (k6_partfun1 @ X0)))),
% 0.21/0.46      inference('sup+', [status(thm)], ['7', '8'])).
% 0.21/0.46  thf(fc3_funct_1, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.21/0.46       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.21/0.46  thf('10', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 0.21/0.46      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.46  thf('11', plain, (![X15 : $i]: ((k6_partfun1 @ X15) = (k6_relat_1 @ X15))),
% 0.21/0.46      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.46  thf('12', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 0.21/0.46      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.46  thf('13', plain, (![X1 : $i]: (v1_funct_1 @ (k6_relat_1 @ X1))),
% 0.21/0.46      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.46  thf('14', plain, (![X15 : $i]: ((k6_partfun1 @ X15) = (k6_relat_1 @ X15))),
% 0.21/0.46      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.46  thf('15', plain, (![X1 : $i]: (v1_funct_1 @ (k6_partfun1 @ X1))),
% 0.21/0.46      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.46  thf('16', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         (((k9_relat_1 @ (k6_partfun1 @ X0) @ X1)
% 0.21/0.46            = (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 0.21/0.46          | ~ (v2_funct_1 @ (k6_partfun1 @ X0)))),
% 0.21/0.46      inference('demod', [status(thm)], ['9', '12', '15'])).
% 0.21/0.46  thf(fc4_funct_1, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.21/0.46       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.21/0.46  thf('17', plain, (![X3 : $i]: (v2_funct_1 @ (k6_relat_1 @ X3))),
% 0.21/0.46      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.21/0.46  thf('18', plain, (![X15 : $i]: ((k6_partfun1 @ X15) = (k6_relat_1 @ X15))),
% 0.21/0.46      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.46  thf('19', plain, (![X3 : $i]: (v2_funct_1 @ (k6_partfun1 @ X3))),
% 0.21/0.46      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.46  thf('20', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         ((k9_relat_1 @ (k6_partfun1 @ X0) @ X1)
% 0.21/0.46           = (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.21/0.46      inference('demod', [status(thm)], ['16', '19'])).
% 0.21/0.46  thf('21', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         ((k8_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 0.21/0.46           = (k9_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.21/0.46      inference('demod', [status(thm)], ['3', '20'])).
% 0.21/0.46  thf('22', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t162_funct_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.46       ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ))).
% 0.21/0.46  thf('23', plain,
% 0.21/0.46      (![X6 : $i, X7 : $i]:
% 0.21/0.46         (((k9_relat_1 @ (k6_relat_1 @ X7) @ X6) = (X6))
% 0.21/0.46          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.21/0.46      inference('cnf', [status(esa)], [t162_funct_1])).
% 0.21/0.46  thf('24', plain, (![X15 : $i]: ((k6_partfun1 @ X15) = (k6_relat_1 @ X15))),
% 0.21/0.46      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.46  thf('25', plain,
% 0.21/0.46      (![X6 : $i, X7 : $i]:
% 0.21/0.46         (((k9_relat_1 @ (k6_partfun1 @ X7) @ X6) = (X6))
% 0.21/0.46          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.21/0.46      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.46  thf('26', plain, (((k9_relat_1 @ (k6_partfun1 @ sk_A) @ sk_B) = (sk_B))),
% 0.21/0.46      inference('sup-', [status(thm)], ['22', '25'])).
% 0.21/0.46  thf('27', plain, (((sk_B) != (sk_B))),
% 0.21/0.46      inference('demod', [status(thm)], ['0', '21', '26'])).
% 0.21/0.46  thf('28', plain, ($false), inference('simplify', [status(thm)], ['27'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
