%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2vKVDYGDMy

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   65 (  86 expanded)
%              Number of leaves         :   26 (  37 expanded)
%              Depth                    :   12
%              Number of atoms          :  416 ( 688 expanded)
%              Number of equality atoms :   12 (  13 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_relset_1_type,type,(
    k6_relset_1: $i > $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( ( k6_relset_1 @ X20 @ X21 @ X18 @ X19 )
        = ( k8_relat_1 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) @ X15 ) ),
    inference(cnf,[status(esa)],[t194_relat_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('13',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ X17 ) @ ( k2_relat_1 @ X16 ) )
      | ~ ( r1_tarski @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('17',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('19',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('20',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('22',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','20','21'])).

thf('23',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('24',plain,
    ( ( k2_xboole_0 @ ( k2_relat_1 @ sk_D ) @ ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    = ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference('sup-',[status(thm)],['10','26'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('28',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ( ( k8_relat_1 @ X13 @ X12 )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k8_relat_1 @ sk_C @ sk_D )
      = sk_D ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['18','19'])).

thf('31',plain,
    ( ( k8_relat_1 @ sk_C @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D ) ),
    inference(demod,[status(thm)],['0','3','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('34',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( r2_relset_1 @ X22 @ X23 @ X24 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['34'])).

thf('36',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['32','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2vKVDYGDMy
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:45:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 76 iterations in 0.041s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(k6_relset_1_type, type, k6_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.49  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.49  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(t36_relset_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.49       ( ( r1_tarski @ B @ C ) =>
% 0.20/0.49         ( r2_relset_1 @ A @ B @ ( k6_relset_1 @ A @ B @ C @ D ) @ D ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.49          ( ( r1_tarski @ B @ C ) =>
% 0.20/0.49            ( r2_relset_1 @ A @ B @ ( k6_relset_1 @ A @ B @ C @ D ) @ D ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t36_relset_1])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      (~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.49          (k6_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(redefinition_k6_relset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.49       ( ( k6_relset_1 @ A @ B @ C @ D ) = ( k8_relat_1 @ C @ D ) ) ))).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.49         (((k6_relset_1 @ X20 @ X21 @ X18 @ X19) = (k8_relat_1 @ X18 @ X19))
% 0.20/0.49          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k6_relset_1])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((k6_relset_1 @ sk_A @ sk_B @ X0 @ sk_D) = (k8_relat_1 @ X0 @ sk_D))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf('4', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t194_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ B ))).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X14 : $i, X15 : $i]:
% 0.20/0.49         (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X14 @ X15)) @ X15)),
% 0.20/0.49      inference('cnf', [status(esa)], [t194_relat_1])).
% 0.20/0.49  thf(t12_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i]:
% 0.20/0.49         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.20/0.49      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((k2_xboole_0 @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0) = (X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.49  thf(t11_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.49          | (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X2 @ X0)) @ X1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X0 @ sk_B)) @ sk_C)),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '9'])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t3_subset, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i]:
% 0.20/0.49         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.49  thf('13', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf(t25_relat_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ A ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( v1_relat_1 @ B ) =>
% 0.20/0.49           ( ( r1_tarski @ A @ B ) =>
% 0.20/0.49             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.20/0.49               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X16 : $i, X17 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X16)
% 0.20/0.49          | (r1_tarski @ (k2_relat_1 @ X17) @ (k2_relat_1 @ X16))
% 0.20/0.49          | ~ (r1_tarski @ X17 @ X16)
% 0.20/0.49          | ~ (v1_relat_1 @ X17))),
% 0.20/0.49      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      ((~ (v1_relat_1 @ sk_D)
% 0.20/0.49        | (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 0.20/0.49           (k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.20/0.49        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(cc2_relat_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ A ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (![X8 : $i, X9 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.20/0.49          | (v1_relat_1 @ X8)
% 0.20/0.49          | ~ (v1_relat_1 @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 0.20/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.49  thf(fc6_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.49  thf('20', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.49      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      ((r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 0.20/0.49        (k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.49      inference('demod', [status(thm)], ['15', '20', '21'])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i]:
% 0.20/0.49         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.20/0.49      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (((k2_xboole_0 @ (k2_relat_1 @ sk_D) @ 
% 0.20/0.49         (k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.20/0.49         = (k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) @ X0)
% 0.20/0.49          | (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.49  thf('27', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 0.20/0.49      inference('sup-', [status(thm)], ['10', '26'])).
% 0.20/0.49  thf(t125_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ B ) =>
% 0.20/0.49       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.20/0.49         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (![X12 : $i, X13 : $i]:
% 0.20/0.49         (~ (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 0.20/0.49          | ((k8_relat_1 @ X13 @ X12) = (X12))
% 0.20/0.49          | ~ (v1_relat_1 @ X12))),
% 0.20/0.49      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      ((~ (v1_relat_1 @ sk_D) | ((k8_relat_1 @ sk_C @ sk_D) = (sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.49  thf('30', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.49      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.49  thf('31', plain, (((k8_relat_1 @ sk_C @ sk_D) = (sk_D))),
% 0.20/0.49      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.49  thf('32', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D)),
% 0.20/0.49      inference('demod', [status(thm)], ['0', '3', '31'])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(reflexivity_r2_relset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.49         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.49       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.49         ((r2_relset_1 @ X22 @ X23 @ X24 @ X24)
% 0.20/0.49          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.20/0.49          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.20/0.49      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.20/0.49      inference('condensation', [status(thm)], ['34'])).
% 0.20/0.49  thf('36', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D)),
% 0.20/0.49      inference('sup-', [status(thm)], ['33', '35'])).
% 0.20/0.49  thf('37', plain, ($false), inference('demod', [status(thm)], ['32', '36'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
