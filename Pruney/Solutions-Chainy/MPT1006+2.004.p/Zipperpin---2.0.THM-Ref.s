%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TgwnE9lHZm

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:07 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   51 (  72 expanded)
%              Number of leaves         :   19 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :  245 ( 350 expanded)
%              Number of equality atoms :   18 (  29 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( m1_subset_1 @ ( k8_relset_1 @ X18 @ X19 @ X17 @ X20 ) @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relset_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_xboole_0 @ X5 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k8_relset_1 @ X0 @ X2 @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('5',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t60_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ k1_xboole_0 @ A )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) )
     => ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ k1_xboole_0 @ A )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) )
       => ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t60_funct_2])).

thf('8',plain,(
    ( k8_relset_1 @ k1_xboole_0 @ sk_A_1 @ sk_C @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k8_relset_1 @ k1_xboole_0 @ sk_A_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( v1_xboole_0 @ ( k8_relset_1 @ k1_xboole_0 @ sk_A_1 @ sk_C @ sk_B ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(rc1_xboole_0,axiom,(
    ? [A: $i] :
      ( v1_xboole_0 @ A ) )).

thf('11',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('12',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('14',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('16',plain,(
    ~ ( v1_xboole_0 @ ( k8_relset_1 @ k1_xboole_0 @ sk_A_1 @ sk_C @ sk_B ) ) ),
    inference('simplify_reflect+',[status(thm)],['10','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('19',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_xboole_0 @ X5 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('22',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('24',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('26',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( v1_xboole_0 @ ( k8_relset_1 @ k1_xboole_0 @ sk_A_1 @ k1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','26'])).

thf('28',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','27'])).

thf('29',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['28','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TgwnE9lHZm
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:34:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.57  % Solved by: fo/fo7.sh
% 0.38/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.57  % done 143 iterations in 0.088s
% 0.38/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.57  % SZS output start Refutation
% 0.38/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.57  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.38/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.57  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.38/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.57  thf(t4_subset_1, axiom,
% 0.38/0.57    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.38/0.57  thf('0', plain,
% 0.38/0.57      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 0.38/0.57      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.38/0.57  thf(dt_k8_relset_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.57       ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.38/0.57  thf('1', plain,
% 0.38/0.57      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.38/0.57          | (m1_subset_1 @ (k8_relset_1 @ X18 @ X19 @ X17 @ X20) @ 
% 0.38/0.57             (k1_zfmisc_1 @ X18)))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_k8_relset_1])).
% 0.38/0.57  thf('2', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.57         (m1_subset_1 @ (k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2) @ 
% 0.38/0.57          (k1_zfmisc_1 @ X1))),
% 0.38/0.57      inference('sup-', [status(thm)], ['0', '1'])).
% 0.38/0.57  thf(cc1_subset_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( v1_xboole_0 @ A ) =>
% 0.38/0.57       ( ![B:$i]:
% 0.38/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.38/0.57  thf('3', plain,
% 0.38/0.57      (![X5 : $i, X6 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.38/0.57          | (v1_xboole_0 @ X5)
% 0.38/0.57          | ~ (v1_xboole_0 @ X6))),
% 0.38/0.57      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.38/0.57  thf('4', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.57         (~ (v1_xboole_0 @ X0)
% 0.38/0.57          | (v1_xboole_0 @ (k8_relset_1 @ X0 @ X2 @ k1_xboole_0 @ X1)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.57  thf(l13_xboole_0, axiom,
% 0.38/0.57    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.38/0.57  thf('5', plain,
% 0.38/0.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.57      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.38/0.57  thf('6', plain,
% 0.38/0.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.57      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.38/0.57  thf('7', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.38/0.57      inference('sup+', [status(thm)], ['5', '6'])).
% 0.38/0.57  thf(t60_funct_2, conjecture,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ k1_xboole_0 @ A ) & 
% 0.38/0.57         ( m1_subset_1 @
% 0.38/0.57           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) ) =>
% 0.38/0.57       ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B ) = ( k1_xboole_0 ) ) ))).
% 0.38/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.38/0.57        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ k1_xboole_0 @ A ) & 
% 0.38/0.57            ( m1_subset_1 @
% 0.38/0.57              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) ) =>
% 0.38/0.57          ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B ) = ( k1_xboole_0 ) ) ) )),
% 0.38/0.57    inference('cnf.neg', [status(esa)], [t60_funct_2])).
% 0.38/0.57  thf('8', plain,
% 0.38/0.57      (((k8_relset_1 @ k1_xboole_0 @ sk_A_1 @ sk_C @ sk_B) != (k1_xboole_0))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('9', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (((X0) != (k1_xboole_0))
% 0.38/0.57          | ~ (v1_xboole_0 @ X0)
% 0.38/0.57          | ~ (v1_xboole_0 @ (k8_relset_1 @ k1_xboole_0 @ sk_A_1 @ sk_C @ sk_B)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.38/0.57  thf('10', plain,
% 0.38/0.57      ((~ (v1_xboole_0 @ (k8_relset_1 @ k1_xboole_0 @ sk_A_1 @ sk_C @ sk_B))
% 0.38/0.57        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.38/0.57      inference('simplify', [status(thm)], ['9'])).
% 0.38/0.57  thf(rc1_xboole_0, axiom, (?[A:$i]: ( v1_xboole_0 @ A ))).
% 0.38/0.57  thf('11', plain, ((v1_xboole_0 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.38/0.57  thf('12', plain, ((v1_xboole_0 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.38/0.57  thf('13', plain,
% 0.38/0.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.57      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.38/0.57  thf('14', plain, (((sk_A) = (k1_xboole_0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['12', '13'])).
% 0.38/0.57  thf('15', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.57      inference('demod', [status(thm)], ['11', '14'])).
% 0.38/0.57  thf('16', plain,
% 0.38/0.57      (~ (v1_xboole_0 @ (k8_relset_1 @ k1_xboole_0 @ sk_A_1 @ sk_C @ sk_B))),
% 0.38/0.57      inference('simplify_reflect+', [status(thm)], ['10', '15'])).
% 0.38/0.57  thf('17', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_C @ 
% 0.38/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_A_1)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(t113_zfmisc_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.38/0.57       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.38/0.57  thf('18', plain,
% 0.38/0.57      (![X2 : $i, X3 : $i]:
% 0.38/0.57         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.38/0.57      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.38/0.57  thf('19', plain,
% 0.38/0.57      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.38/0.57      inference('simplify', [status(thm)], ['18'])).
% 0.38/0.57  thf('20', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.38/0.57      inference('demod', [status(thm)], ['17', '19'])).
% 0.38/0.57  thf('21', plain,
% 0.38/0.57      (![X5 : $i, X6 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.38/0.57          | (v1_xboole_0 @ X5)
% 0.38/0.57          | ~ (v1_xboole_0 @ X6))),
% 0.38/0.57      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.38/0.57  thf('22', plain, ((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_C))),
% 0.38/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.38/0.57  thf('23', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.57      inference('demod', [status(thm)], ['11', '14'])).
% 0.38/0.57  thf('24', plain, ((v1_xboole_0 @ sk_C)),
% 0.38/0.57      inference('demod', [status(thm)], ['22', '23'])).
% 0.38/0.57  thf('25', plain,
% 0.38/0.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.57      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.38/0.57  thf('26', plain, (((sk_C) = (k1_xboole_0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.57  thf('27', plain,
% 0.38/0.57      (~ (v1_xboole_0 @ 
% 0.38/0.57          (k8_relset_1 @ k1_xboole_0 @ sk_A_1 @ k1_xboole_0 @ sk_B))),
% 0.38/0.57      inference('demod', [status(thm)], ['16', '26'])).
% 0.38/0.57  thf('28', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.57      inference('sup-', [status(thm)], ['4', '27'])).
% 0.38/0.57  thf('29', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.57      inference('demod', [status(thm)], ['11', '14'])).
% 0.38/0.57  thf('30', plain, ($false), inference('demod', [status(thm)], ['28', '29'])).
% 0.38/0.57  
% 0.38/0.57  % SZS output end Refutation
% 0.38/0.57  
% 0.38/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
