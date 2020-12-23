%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XjDKPbaoXN

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:29 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   57 (  78 expanded)
%              Number of leaves         :   25 (  34 expanded)
%              Depth                    :   13
%              Number of atoms          :  368 ( 626 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k6_relset_1_type,type,(
    k6_relset_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( ( k6_relset_1 @ X19 @ X20 @ X17 @ X18 )
        = ( k8_relat_1 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D )
      = ( k8_relat_1 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( m1_subset_1 @ ( k8_relat_1 @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf(t116_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ A ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X7 @ X8 ) ) @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t116_relat_1])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v4_relat_1 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('9',plain,(
    v4_relat_1 @ sk_D @ sk_C ),
    inference('sup-',[status(thm)],['7','8'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('10',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v4_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_C ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('14',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_C ),
    inference(demod,[status(thm)],['11','14'])).

thf(l29_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ B ) ) ) )).

thf('16',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k8_relat_1 @ X9 @ X10 ) ) @ ( k1_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l29_wellord1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ sk_C )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['12','13'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('22',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X21 ) @ X22 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X21 ) @ X23 )
      | ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) )
      | ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['6','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['12','13'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['12','13'])).

thf('29',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['4','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XjDKPbaoXN
% 0.16/0.37  % Computer   : n020.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 19:17:37 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.23/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.53  % Solved by: fo/fo7.sh
% 0.23/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.53  % done 58 iterations in 0.046s
% 0.23/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.53  % SZS output start Refutation
% 0.23/0.53  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.23/0.53  thf(k6_relset_1_type, type, k6_relset_1: $i > $i > $i > $i > $i).
% 0.23/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.53  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.23/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.23/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.23/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.23/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.53  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.23/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.53  thf(t35_relset_1, conjecture,
% 0.23/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.53     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.23/0.53       ( m1_subset_1 @
% 0.23/0.53         ( k6_relset_1 @ C @ A @ B @ D ) @ 
% 0.23/0.53         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 0.23/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.53    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.53        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.23/0.53          ( m1_subset_1 @
% 0.23/0.53            ( k6_relset_1 @ C @ A @ B @ D ) @ 
% 0.23/0.53            ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )),
% 0.23/0.53    inference('cnf.neg', [status(esa)], [t35_relset_1])).
% 0.23/0.53  thf('0', plain,
% 0.23/0.53      (~ (m1_subset_1 @ (k6_relset_1 @ sk_C @ sk_A @ sk_B @ sk_D) @ 
% 0.23/0.53          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('1', plain,
% 0.23/0.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf(redefinition_k6_relset_1, axiom,
% 0.23/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.53     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.53       ( ( k6_relset_1 @ A @ B @ C @ D ) = ( k8_relat_1 @ C @ D ) ) ))).
% 0.23/0.53  thf('2', plain,
% 0.23/0.53      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.23/0.53         (((k6_relset_1 @ X19 @ X20 @ X17 @ X18) = (k8_relat_1 @ X17 @ X18))
% 0.23/0.53          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.23/0.53      inference('cnf', [status(esa)], [redefinition_k6_relset_1])).
% 0.23/0.53  thf('3', plain,
% 0.23/0.53      (![X0 : $i]:
% 0.23/0.53         ((k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D) = (k8_relat_1 @ X0 @ sk_D))),
% 0.23/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.53  thf('4', plain,
% 0.23/0.53      (~ (m1_subset_1 @ (k8_relat_1 @ sk_B @ sk_D) @ 
% 0.23/0.53          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.23/0.53      inference('demod', [status(thm)], ['0', '3'])).
% 0.23/0.53  thf(dt_k8_relat_1, axiom,
% 0.23/0.53    (![A:$i,B:$i]:
% 0.23/0.53     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 0.23/0.53  thf('5', plain,
% 0.23/0.53      (![X5 : $i, X6 : $i]:
% 0.23/0.53         ((v1_relat_1 @ (k8_relat_1 @ X5 @ X6)) | ~ (v1_relat_1 @ X6))),
% 0.23/0.53      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.23/0.53  thf(t116_relat_1, axiom,
% 0.23/0.53    (![A:$i,B:$i]:
% 0.23/0.53     ( ( v1_relat_1 @ B ) =>
% 0.23/0.53       ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ A ) ))).
% 0.23/0.53  thf('6', plain,
% 0.23/0.53      (![X7 : $i, X8 : $i]:
% 0.23/0.53         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X7 @ X8)) @ X7)
% 0.23/0.53          | ~ (v1_relat_1 @ X8))),
% 0.23/0.53      inference('cnf', [status(esa)], [t116_relat_1])).
% 0.23/0.53  thf('7', plain,
% 0.23/0.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf(cc2_relset_1, axiom,
% 0.23/0.53    (![A:$i,B:$i,C:$i]:
% 0.23/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.53       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.23/0.53  thf('8', plain,
% 0.23/0.53      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.23/0.53         ((v4_relat_1 @ X14 @ X15)
% 0.23/0.53          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.23/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.23/0.53  thf('9', plain, ((v4_relat_1 @ sk_D @ sk_C)),
% 0.23/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.23/0.53  thf(d18_relat_1, axiom,
% 0.23/0.53    (![A:$i,B:$i]:
% 0.23/0.53     ( ( v1_relat_1 @ B ) =>
% 0.23/0.53       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.23/0.53  thf('10', plain,
% 0.23/0.53      (![X3 : $i, X4 : $i]:
% 0.23/0.53         (~ (v4_relat_1 @ X3 @ X4)
% 0.23/0.53          | (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 0.23/0.53          | ~ (v1_relat_1 @ X3))),
% 0.23/0.53      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.23/0.53  thf('11', plain,
% 0.23/0.53      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_C))),
% 0.23/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.23/0.53  thf('12', plain,
% 0.23/0.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf(cc1_relset_1, axiom,
% 0.23/0.53    (![A:$i,B:$i,C:$i]:
% 0.23/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.53       ( v1_relat_1 @ C ) ))).
% 0.23/0.53  thf('13', plain,
% 0.23/0.53      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.23/0.53         ((v1_relat_1 @ X11)
% 0.23/0.53          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.23/0.53      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.23/0.53  thf('14', plain, ((v1_relat_1 @ sk_D)),
% 0.23/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.23/0.53  thf('15', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_C)),
% 0.23/0.53      inference('demod', [status(thm)], ['11', '14'])).
% 0.23/0.53  thf(l29_wellord1, axiom,
% 0.23/0.53    (![A:$i,B:$i]:
% 0.23/0.53     ( ( v1_relat_1 @ B ) =>
% 0.23/0.53       ( r1_tarski @
% 0.23/0.53         ( k1_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ B ) ) ))).
% 0.23/0.53  thf('16', plain,
% 0.23/0.53      (![X9 : $i, X10 : $i]:
% 0.23/0.53         ((r1_tarski @ (k1_relat_1 @ (k8_relat_1 @ X9 @ X10)) @ 
% 0.23/0.53           (k1_relat_1 @ X10))
% 0.23/0.53          | ~ (v1_relat_1 @ X10))),
% 0.23/0.53      inference('cnf', [status(esa)], [l29_wellord1])).
% 0.23/0.53  thf(t1_xboole_1, axiom,
% 0.23/0.53    (![A:$i,B:$i,C:$i]:
% 0.23/0.53     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.23/0.53       ( r1_tarski @ A @ C ) ))).
% 0.23/0.53  thf('17', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.53         (~ (r1_tarski @ X0 @ X1)
% 0.23/0.53          | ~ (r1_tarski @ X1 @ X2)
% 0.23/0.53          | (r1_tarski @ X0 @ X2))),
% 0.23/0.53      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.23/0.53  thf('18', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.53         (~ (v1_relat_1 @ X0)
% 0.23/0.53          | (r1_tarski @ (k1_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X2)
% 0.23/0.53          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ X2))),
% 0.23/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.23/0.53  thf('19', plain,
% 0.23/0.53      (![X0 : $i]:
% 0.23/0.53         ((r1_tarski @ (k1_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ sk_C)
% 0.23/0.53          | ~ (v1_relat_1 @ sk_D))),
% 0.23/0.53      inference('sup-', [status(thm)], ['15', '18'])).
% 0.23/0.53  thf('20', plain, ((v1_relat_1 @ sk_D)),
% 0.23/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.23/0.53  thf('21', plain,
% 0.23/0.53      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ sk_C)),
% 0.23/0.53      inference('demod', [status(thm)], ['19', '20'])).
% 0.23/0.53  thf(t11_relset_1, axiom,
% 0.23/0.53    (![A:$i,B:$i,C:$i]:
% 0.23/0.53     ( ( v1_relat_1 @ C ) =>
% 0.23/0.53       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.23/0.53           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.23/0.53         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.23/0.53  thf('22', plain,
% 0.23/0.53      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.23/0.53         (~ (r1_tarski @ (k1_relat_1 @ X21) @ X22)
% 0.23/0.53          | ~ (r1_tarski @ (k2_relat_1 @ X21) @ X23)
% 0.23/0.53          | (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.23/0.53          | ~ (v1_relat_1 @ X21))),
% 0.23/0.53      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.23/0.53  thf('23', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i]:
% 0.23/0.53         (~ (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_D))
% 0.23/0.53          | (m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 0.23/0.53             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 0.23/0.53          | ~ (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ X1))),
% 0.23/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.23/0.53  thf('24', plain,
% 0.23/0.53      (![X0 : $i]:
% 0.23/0.53         (~ (v1_relat_1 @ sk_D)
% 0.23/0.53          | (m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 0.23/0.53             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X0)))
% 0.23/0.53          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_D)))),
% 0.23/0.53      inference('sup-', [status(thm)], ['6', '23'])).
% 0.23/0.53  thf('25', plain, ((v1_relat_1 @ sk_D)),
% 0.23/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.23/0.53  thf('26', plain,
% 0.23/0.53      (![X0 : $i]:
% 0.23/0.53         ((m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 0.23/0.53           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X0)))
% 0.23/0.53          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_D)))),
% 0.23/0.53      inference('demod', [status(thm)], ['24', '25'])).
% 0.23/0.53  thf('27', plain,
% 0.23/0.53      (![X0 : $i]:
% 0.23/0.53         (~ (v1_relat_1 @ sk_D)
% 0.23/0.53          | (m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 0.23/0.53             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X0))))),
% 0.23/0.53      inference('sup-', [status(thm)], ['5', '26'])).
% 0.23/0.53  thf('28', plain, ((v1_relat_1 @ sk_D)),
% 0.23/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.23/0.53  thf('29', plain,
% 0.23/0.53      (![X0 : $i]:
% 0.23/0.53         (m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 0.23/0.53          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X0)))),
% 0.23/0.53      inference('demod', [status(thm)], ['27', '28'])).
% 0.23/0.53  thf('30', plain, ($false), inference('demod', [status(thm)], ['4', '29'])).
% 0.23/0.53  
% 0.23/0.53  % SZS output end Refutation
% 0.23/0.53  
% 0.23/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
