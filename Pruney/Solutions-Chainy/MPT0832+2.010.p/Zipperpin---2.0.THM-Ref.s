%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3iZVvmWfjG

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:29 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   46 (  62 expanded)
%              Number of leaves         :   21 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :  327 ( 559 expanded)
%              Number of equality atoms :    9 (  13 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relset_1_type,type,(
    k6_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t35_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
     => ( m1_subset_1 @ ( k6_relset_1 @ C @ A @ B @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
       => ( m1_subset_1 @ ( k6_relset_1 @ C @ A @ B @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_relset_1])).

thf('0',plain,(
    ~ ( m1_subset_1 @ ( k6_relset_1 @ sk_C @ sk_A @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k6_relset_1 @ A @ B @ C @ D )
        = ( k8_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( ( k6_relset_1 @ X15 @ X16 @ X13 @ X14 )
        = ( k8_relat_1 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D )
      = ( k8_relat_1 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( m1_subset_1 @ ( k8_relat_1 @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t119_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X5 @ X4 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X4 ) @ X5 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k6_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( m1_subset_1 @ ( k6_relset_1 @ X9 @ X10 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t14_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) )).

thf('13',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X17 ) @ X18 )
      | ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[t14_relset_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D )
      = ( k8_relat_1 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D )
      = ( k8_relat_1 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('20',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('21',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['4','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3iZVvmWfjG
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:56:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 58 iterations in 0.037s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.48  thf(k6_relset_1_type, type, k6_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.48  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.20/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(t35_relset_1, conjecture,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.20/0.48       ( m1_subset_1 @
% 0.20/0.48         ( k6_relset_1 @ C @ A @ B @ D ) @ 
% 0.20/0.48         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.20/0.48          ( m1_subset_1 @
% 0.20/0.48            ( k6_relset_1 @ C @ A @ B @ D ) @ 
% 0.20/0.48            ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t35_relset_1])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (~ (m1_subset_1 @ (k6_relset_1 @ sk_C @ sk_A @ sk_B @ sk_D) @ 
% 0.20/0.48          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(redefinition_k6_relset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.48       ( ( k6_relset_1 @ A @ B @ C @ D ) = ( k8_relat_1 @ C @ D ) ) ))).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.48         (((k6_relset_1 @ X15 @ X16 @ X13 @ X14) = (k8_relat_1 @ X13 @ X14))
% 0.20/0.48          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k6_relset_1])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D) = (k8_relat_1 @ X0 @ sk_D))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (~ (m1_subset_1 @ (k8_relat_1 @ sk_B @ sk_D) @ 
% 0.20/0.48          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.20/0.48      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.48  thf(t119_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ B ) =>
% 0.20/0.48       ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) =
% 0.20/0.48         ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i]:
% 0.20/0.48         (((k2_relat_1 @ (k8_relat_1 @ X5 @ X4))
% 0.20/0.48            = (k3_xboole_0 @ (k2_relat_1 @ X4) @ X5))
% 0.20/0.48          | ~ (v1_relat_1 @ X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [t119_relat_1])).
% 0.20/0.48  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.48  thf(t17_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X2 : $i, X3 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ X2)),
% 0.20/0.48      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.20/0.48      inference('sup+', [status(thm)], ['6', '7'])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X1)
% 0.20/0.48          | ~ (v1_relat_1 @ X0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['5', '8'])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(dt_k6_relset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.48       ( m1_subset_1 @
% 0.20/0.48         ( k6_relset_1 @ A @ B @ C @ D ) @ 
% 0.20/0.48         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ))).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.48         ((m1_subset_1 @ (k6_relset_1 @ X9 @ X10 @ X11 @ X12) @ 
% 0.20/0.48           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.20/0.48          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k6_relset_1])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (m1_subset_1 @ (k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D) @ 
% 0.20/0.48          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.48  thf(t14_relset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.20/0.48       ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B ) =>
% 0.20/0.48         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ))).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.48         (~ (r1_tarski @ (k2_relat_1 @ X17) @ X18)
% 0.20/0.48          | (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X18)))
% 0.20/0.48          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.20/0.48      inference('cnf', [status(esa)], [t14_relset_1])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((m1_subset_1 @ (k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D) @ 
% 0.20/0.48           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 0.20/0.48          | ~ (r1_tarski @ 
% 0.20/0.48               (k2_relat_1 @ (k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D)) @ X1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D) = (k8_relat_1 @ X0 @ sk_D))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D) = (k8_relat_1 @ X0 @ sk_D))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 0.20/0.48           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 0.20/0.48          | ~ (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ X1))),
% 0.20/0.48      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ sk_D)
% 0.20/0.48          | (m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 0.20/0.48             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X0))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['9', '17'])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(cc1_relset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.48       ( v1_relat_1 @ C ) ))).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.48         ((v1_relat_1 @ X6)
% 0.20/0.48          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.20/0.48      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.48  thf('21', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.48      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 0.20/0.48          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X0)))),
% 0.20/0.48      inference('demod', [status(thm)], ['18', '21'])).
% 0.20/0.48  thf('23', plain, ($false), inference('demod', [status(thm)], ['4', '22'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
