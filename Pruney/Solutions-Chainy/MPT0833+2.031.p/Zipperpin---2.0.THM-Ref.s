%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CBkZvMJXGB

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:37 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   59 (  79 expanded)
%              Number of leaves         :   24 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :  381 ( 646 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k6_relset_1_type,type,(
    k6_relset_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t36_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( r1_tarski @ B @ C )
       => ( r2_relset_1 @ A @ B @ ( k6_relset_1 @ A @ B @ C @ D ) @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
       => ( ( r1_tarski @ B @ C )
         => ( r2_relset_1 @ A @ B @ ( k6_relset_1 @ A @ B @ C @ D ) @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_relset_1])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k6_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k6_relset_1 @ A @ B @ C @ D )
        = ( k8_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( ( k6_relset_1 @ X21 @ X22 @ X19 @ X20 )
        = ( k8_relat_1 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k6_relset_1 @ sk_A @ sk_B @ X0 @ sk_D )
      = ( k8_relat_1 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t194_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ B ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) @ X16 ) ),
    inference(cnf,[status(esa)],[t194_relat_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( r1_tarski @ ( k2_relat_1 @ X18 ) @ ( k2_relat_1 @ X17 ) )
      | ~ ( r1_tarski @ X18 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('18',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('20',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference('sup-',[status(thm)],['8','22'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('24',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ( ( k8_relat_1 @ X14 @ X13 )
        = X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k8_relat_1 @ sk_C @ sk_D )
      = sk_D ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['16','17'])).

thf('27',plain,
    ( ( k8_relat_1 @ sk_C @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D ) ),
    inference(demod,[status(thm)],['0','3','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('30',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( r2_relset_1 @ X24 @ X25 @ X23 @ X26 )
      | ( X23 != X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('31',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r2_relset_1 @ X24 @ X25 @ X26 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    $false ),
    inference(demod,[status(thm)],['28','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CBkZvMJXGB
% 0.15/0.34  % Computer   : n018.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 15:33:12 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.37/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.59  % Solved by: fo/fo7.sh
% 0.37/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.59  % done 164 iterations in 0.124s
% 0.37/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.59  % SZS output start Refutation
% 0.37/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.59  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.37/0.59  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.37/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.59  thf(sk_D_type, type, sk_D: $i).
% 0.37/0.59  thf(k6_relset_1_type, type, k6_relset_1: $i > $i > $i > $i > $i).
% 0.37/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.59  thf(t36_relset_1, conjecture,
% 0.37/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.59     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.59       ( ( r1_tarski @ B @ C ) =>
% 0.37/0.59         ( r2_relset_1 @ A @ B @ ( k6_relset_1 @ A @ B @ C @ D ) @ D ) ) ))).
% 0.37/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.59    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.59        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.59          ( ( r1_tarski @ B @ C ) =>
% 0.37/0.59            ( r2_relset_1 @ A @ B @ ( k6_relset_1 @ A @ B @ C @ D ) @ D ) ) ) )),
% 0.37/0.59    inference('cnf.neg', [status(esa)], [t36_relset_1])).
% 0.37/0.59  thf('0', plain,
% 0.37/0.59      (~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.37/0.59          (k6_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('1', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf(redefinition_k6_relset_1, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.59     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.59       ( ( k6_relset_1 @ A @ B @ C @ D ) = ( k8_relat_1 @ C @ D ) ) ))).
% 0.37/0.59  thf('2', plain,
% 0.37/0.59      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.37/0.59         (((k6_relset_1 @ X21 @ X22 @ X19 @ X20) = (k8_relat_1 @ X19 @ X20))
% 0.37/0.59          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.37/0.59      inference('cnf', [status(esa)], [redefinition_k6_relset_1])).
% 0.37/0.59  thf('3', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         ((k6_relset_1 @ sk_A @ sk_B @ X0 @ sk_D) = (k8_relat_1 @ X0 @ sk_D))),
% 0.37/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.59  thf('4', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf(t194_relat_1, axiom,
% 0.37/0.59    (![A:$i,B:$i]: ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ B ))).
% 0.37/0.59  thf('5', plain,
% 0.37/0.59      (![X15 : $i, X16 : $i]:
% 0.37/0.59         (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X15 @ X16)) @ X16)),
% 0.37/0.59      inference('cnf', [status(esa)], [t194_relat_1])).
% 0.37/0.59  thf(t1_xboole_1, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i]:
% 0.37/0.59     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.37/0.59       ( r1_tarski @ A @ C ) ))).
% 0.37/0.59  thf('6', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.59         (~ (r1_tarski @ X0 @ X1)
% 0.37/0.59          | ~ (r1_tarski @ X1 @ X2)
% 0.37/0.59          | (r1_tarski @ X0 @ X2))),
% 0.37/0.59      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.37/0.59  thf('7', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.59         ((r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X2)
% 0.37/0.59          | ~ (r1_tarski @ X0 @ X2))),
% 0.37/0.59      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.59  thf('8', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X0 @ sk_B)) @ sk_C)),
% 0.37/0.59      inference('sup-', [status(thm)], ['4', '7'])).
% 0.37/0.59  thf('9', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf(t3_subset, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.59  thf('10', plain,
% 0.37/0.59      (![X6 : $i, X7 : $i]:
% 0.37/0.59         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.37/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.59  thf('11', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.37/0.59      inference('sup-', [status(thm)], ['9', '10'])).
% 0.37/0.59  thf(t25_relat_1, axiom,
% 0.37/0.59    (![A:$i]:
% 0.37/0.59     ( ( v1_relat_1 @ A ) =>
% 0.37/0.59       ( ![B:$i]:
% 0.37/0.59         ( ( v1_relat_1 @ B ) =>
% 0.37/0.59           ( ( r1_tarski @ A @ B ) =>
% 0.37/0.59             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.37/0.59               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.37/0.59  thf('12', plain,
% 0.37/0.59      (![X17 : $i, X18 : $i]:
% 0.37/0.59         (~ (v1_relat_1 @ X17)
% 0.37/0.59          | (r1_tarski @ (k2_relat_1 @ X18) @ (k2_relat_1 @ X17))
% 0.37/0.59          | ~ (r1_tarski @ X18 @ X17)
% 0.37/0.59          | ~ (v1_relat_1 @ X18))),
% 0.37/0.59      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.37/0.59  thf('13', plain,
% 0.37/0.59      ((~ (v1_relat_1 @ sk_D)
% 0.37/0.59        | (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 0.37/0.59           (k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.37/0.59        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.59  thf('14', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf(cc2_relat_1, axiom,
% 0.37/0.59    (![A:$i]:
% 0.37/0.59     ( ( v1_relat_1 @ A ) =>
% 0.37/0.59       ( ![B:$i]:
% 0.37/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.37/0.59  thf('15', plain,
% 0.37/0.59      (![X9 : $i, X10 : $i]:
% 0.37/0.59         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.37/0.59          | (v1_relat_1 @ X9)
% 0.37/0.59          | ~ (v1_relat_1 @ X10))),
% 0.37/0.59      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.37/0.59  thf('16', plain,
% 0.37/0.59      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 0.37/0.59      inference('sup-', [status(thm)], ['14', '15'])).
% 0.37/0.59  thf(fc6_relat_1, axiom,
% 0.37/0.59    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.37/0.59  thf('17', plain,
% 0.37/0.59      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 0.37/0.59      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.37/0.59  thf('18', plain, ((v1_relat_1 @ sk_D)),
% 0.37/0.59      inference('demod', [status(thm)], ['16', '17'])).
% 0.37/0.59  thf('19', plain,
% 0.37/0.59      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 0.37/0.59      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.37/0.59  thf('20', plain,
% 0.37/0.59      ((r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 0.37/0.59        (k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.37/0.59      inference('demod', [status(thm)], ['13', '18', '19'])).
% 0.37/0.59  thf('21', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.59         (~ (r1_tarski @ X0 @ X1)
% 0.37/0.59          | ~ (r1_tarski @ X1 @ X2)
% 0.37/0.59          | (r1_tarski @ X0 @ X2))),
% 0.37/0.59      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.37/0.59  thf('22', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         ((r1_tarski @ (k2_relat_1 @ sk_D) @ X0)
% 0.37/0.59          | ~ (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) @ X0))),
% 0.37/0.59      inference('sup-', [status(thm)], ['20', '21'])).
% 0.37/0.59  thf('23', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 0.37/0.59      inference('sup-', [status(thm)], ['8', '22'])).
% 0.37/0.59  thf(t125_relat_1, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( v1_relat_1 @ B ) =>
% 0.37/0.59       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.37/0.59         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.37/0.59  thf('24', plain,
% 0.37/0.59      (![X13 : $i, X14 : $i]:
% 0.37/0.59         (~ (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 0.37/0.59          | ((k8_relat_1 @ X14 @ X13) = (X13))
% 0.37/0.59          | ~ (v1_relat_1 @ X13))),
% 0.37/0.59      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.37/0.59  thf('25', plain,
% 0.37/0.59      ((~ (v1_relat_1 @ sk_D) | ((k8_relat_1 @ sk_C @ sk_D) = (sk_D)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['23', '24'])).
% 0.37/0.59  thf('26', plain, ((v1_relat_1 @ sk_D)),
% 0.37/0.59      inference('demod', [status(thm)], ['16', '17'])).
% 0.37/0.59  thf('27', plain, (((k8_relat_1 @ sk_C @ sk_D) = (sk_D))),
% 0.37/0.59      inference('demod', [status(thm)], ['25', '26'])).
% 0.37/0.59  thf('28', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D)),
% 0.37/0.59      inference('demod', [status(thm)], ['0', '3', '27'])).
% 0.37/0.59  thf('29', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf(redefinition_r2_relset_1, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.59     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.37/0.59         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.59       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.37/0.59  thf('30', plain,
% 0.37/0.59      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.37/0.59         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.37/0.59          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.37/0.59          | (r2_relset_1 @ X24 @ X25 @ X23 @ X26)
% 0.37/0.59          | ((X23) != (X26)))),
% 0.37/0.59      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.37/0.59  thf('31', plain,
% 0.37/0.59      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.37/0.59         ((r2_relset_1 @ X24 @ X25 @ X26 @ X26)
% 0.37/0.59          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.37/0.59      inference('simplify', [status(thm)], ['30'])).
% 0.37/0.59  thf('32', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D)),
% 0.37/0.59      inference('sup-', [status(thm)], ['29', '31'])).
% 0.37/0.59  thf('33', plain, ($false), inference('demod', [status(thm)], ['28', '32'])).
% 0.37/0.59  
% 0.37/0.59  % SZS output end Refutation
% 0.37/0.59  
% 0.37/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
