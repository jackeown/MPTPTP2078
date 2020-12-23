%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3j0PPBUFci

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:31 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   58 (  72 expanded)
%              Number of leaves         :   27 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :  319 ( 407 expanded)
%              Number of equality atoms :   31 (  44 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X18: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( ( k8_relset_1 @ X14 @ X15 @ X13 @ X16 )
        = ( k10_relat_1 @ X13 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X12 ) @ ( k6_relat_1 @ X11 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X19: $i] :
      ( ( k6_partfun1 @ X19 )
      = ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('6',plain,(
    ! [X19: $i] :
      ( ( k6_partfun1 @ X19 )
      = ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('7',plain,(
    ! [X19: $i] :
      ( ( k6_partfun1 @ X19 )
      = ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X12 ) @ ( k6_partfun1 @ X11 ) )
      = ( k6_partfun1 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('9',plain,(
    ! [X7: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X7 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('10',plain,(
    ! [X19: $i] :
      ( ( k6_partfun1 @ X19 )
      = ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('11',plain,(
    ! [X7: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X7 ) )
      = X7 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) )
        = ( k10_relat_1 @ X6 @ ( k1_relat_1 @ X5 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('14',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('15',plain,(
    ! [X19: $i] :
      ( ( k6_partfun1 @ X19 )
      = ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('16',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X9 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k6_partfun1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','17'])).

thf('19',plain,(
    ! [X7: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X7 ) )
      = X7 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('20',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X9 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('25',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('27',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    sk_B != sk_B ),
    inference(demod,[status(thm)],['0','22','27'])).

thf('29',plain,(
    $false ),
    inference(simplify,[status(thm)],['28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3j0PPBUFci
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:59:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 25 iterations in 0.015s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.19/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.48  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.19/0.48  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.19/0.48  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.19/0.48  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.19/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.48  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.19/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.48  thf(t171_funct_2, conjecture,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.48       ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i,B:$i]:
% 0.19/0.48        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.48          ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t171_funct_2])).
% 0.19/0.48  thf('0', plain,
% 0.19/0.48      (((k8_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ sk_B) != (sk_B))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(dt_k6_partfun1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( m1_subset_1 @
% 0.19/0.48         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.19/0.48       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.19/0.48  thf('1', plain,
% 0.19/0.48      (![X18 : $i]:
% 0.19/0.48         (m1_subset_1 @ (k6_partfun1 @ X18) @ 
% 0.19/0.48          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))),
% 0.19/0.48      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.19/0.48  thf(redefinition_k8_relset_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.48       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.19/0.48  thf('2', plain,
% 0.19/0.48      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.19/0.48          | ((k8_relset_1 @ X14 @ X15 @ X13 @ X16) = (k10_relat_1 @ X13 @ X16)))),
% 0.19/0.48      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((k8_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 0.19/0.48           = (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.19/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.48  thf(t43_funct_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.19/0.48       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.48  thf('4', plain,
% 0.19/0.48      (![X11 : $i, X12 : $i]:
% 0.19/0.48         ((k5_relat_1 @ (k6_relat_1 @ X12) @ (k6_relat_1 @ X11))
% 0.19/0.48           = (k6_relat_1 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.19/0.48  thf(redefinition_k6_partfun1, axiom,
% 0.19/0.48    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.19/0.48  thf('5', plain, (![X19 : $i]: ((k6_partfun1 @ X19) = (k6_relat_1 @ X19))),
% 0.19/0.48      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.19/0.48  thf('6', plain, (![X19 : $i]: ((k6_partfun1 @ X19) = (k6_relat_1 @ X19))),
% 0.19/0.48      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.19/0.48  thf('7', plain, (![X19 : $i]: ((k6_partfun1 @ X19) = (k6_relat_1 @ X19))),
% 0.19/0.48      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.19/0.48  thf('8', plain,
% 0.19/0.48      (![X11 : $i, X12 : $i]:
% 0.19/0.48         ((k5_relat_1 @ (k6_partfun1 @ X12) @ (k6_partfun1 @ X11))
% 0.19/0.48           = (k6_partfun1 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.19/0.48      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.19/0.48  thf(t71_relat_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.19/0.48       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.19/0.48  thf('9', plain, (![X7 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X7)) = (X7))),
% 0.19/0.48      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.48  thf('10', plain, (![X19 : $i]: ((k6_partfun1 @ X19) = (k6_relat_1 @ X19))),
% 0.19/0.48      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.19/0.48  thf('11', plain, (![X7 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X7)) = (X7))),
% 0.19/0.48      inference('demod', [status(thm)], ['9', '10'])).
% 0.19/0.48  thf(t182_relat_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( v1_relat_1 @ A ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( v1_relat_1 @ B ) =>
% 0.19/0.48           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.19/0.48             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.19/0.48  thf('12', plain,
% 0.19/0.48      (![X5 : $i, X6 : $i]:
% 0.19/0.48         (~ (v1_relat_1 @ X5)
% 0.19/0.48          | ((k1_relat_1 @ (k5_relat_1 @ X6 @ X5))
% 0.19/0.48              = (k10_relat_1 @ X6 @ (k1_relat_1 @ X5)))
% 0.19/0.48          | ~ (v1_relat_1 @ X6))),
% 0.19/0.48      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.19/0.48  thf('13', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0)))
% 0.19/0.48            = (k10_relat_1 @ X1 @ X0))
% 0.19/0.48          | ~ (v1_relat_1 @ X1)
% 0.19/0.48          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 0.19/0.48      inference('sup+', [status(thm)], ['11', '12'])).
% 0.19/0.48  thf(fc3_funct_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.19/0.48       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.19/0.48  thf('14', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.19/0.48      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.48  thf('15', plain, (![X19 : $i]: ((k6_partfun1 @ X19) = (k6_relat_1 @ X19))),
% 0.19/0.48      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.19/0.48  thf('16', plain, (![X9 : $i]: (v1_relat_1 @ (k6_partfun1 @ X9))),
% 0.19/0.48      inference('demod', [status(thm)], ['14', '15'])).
% 0.19/0.48  thf('17', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0)))
% 0.19/0.48            = (k10_relat_1 @ X1 @ X0))
% 0.19/0.48          | ~ (v1_relat_1 @ X1))),
% 0.19/0.48      inference('demod', [status(thm)], ['13', '16'])).
% 0.19/0.48  thf('18', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (((k1_relat_1 @ (k6_partfun1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.19/0.48            = (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 0.19/0.48          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 0.19/0.48      inference('sup+', [status(thm)], ['8', '17'])).
% 0.19/0.48  thf('19', plain, (![X7 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X7)) = (X7))),
% 0.19/0.48      inference('demod', [status(thm)], ['9', '10'])).
% 0.19/0.48  thf('20', plain, (![X9 : $i]: (v1_relat_1 @ (k6_partfun1 @ X9))),
% 0.19/0.48      inference('demod', [status(thm)], ['14', '15'])).
% 0.19/0.48  thf('21', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((k3_xboole_0 @ X1 @ X0) = (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.19/0.48      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.19/0.48  thf('22', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((k8_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 0.19/0.48           = (k3_xboole_0 @ X1 @ X0))),
% 0.19/0.48      inference('demod', [status(thm)], ['3', '21'])).
% 0.19/0.48  thf('23', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t3_subset, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.48  thf('24', plain,
% 0.19/0.48      (![X2 : $i, X3 : $i]:
% 0.19/0.48         ((r1_tarski @ X2 @ X3) | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.48  thf('25', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.19/0.48      inference('sup-', [status(thm)], ['23', '24'])).
% 0.19/0.48  thf(t28_xboole_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.48  thf('26', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.19/0.48      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.48  thf('27', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.19/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.19/0.48  thf('28', plain, (((sk_B) != (sk_B))),
% 0.19/0.48      inference('demod', [status(thm)], ['0', '22', '27'])).
% 0.19/0.48  thf('29', plain, ($false), inference('simplify', [status(thm)], ['28'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
