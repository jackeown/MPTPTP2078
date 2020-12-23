%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6nP515tTli

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:28 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   54 (  84 expanded)
%              Number of leaves         :   23 (  36 expanded)
%              Depth                    :   12
%              Number of atoms          :  406 ( 812 expanded)
%              Number of equality atoms :    5 (   9 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_relset_1_type,type,(
    k6_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( ( k6_relset_1 @ X18 @ X19 @ X16 @ X17 )
        = ( k8_relat_1 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D )
      = ( k8_relat_1 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( m1_subset_1 @ ( k8_relat_1 @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t116_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ A ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X4 @ X5 ) ) @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t116_relat_1])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k6_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( m1_subset_1 @ ( k6_relset_1 @ X12 @ X13 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v4_relat_1 @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D ) @ sk_C ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D ) ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('14',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['12','15'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('17',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X20 ) @ X22 )
      | ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D ) )
      | ( m1_subset_1 @ ( k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D )
      = ( k8_relat_1 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D )
      = ( k8_relat_1 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('27',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['4','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6nP515tTli
% 0.16/0.36  % Computer   : n005.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 15:23:18 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.23/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.51  % Solved by: fo/fo7.sh
% 0.23/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.51  % done 50 iterations in 0.029s
% 0.23/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.51  % SZS output start Refutation
% 0.23/0.51  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.23/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.51  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.23/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.23/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.23/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.51  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.23/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.23/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.51  thf(k6_relset_1_type, type, k6_relset_1: $i > $i > $i > $i > $i).
% 0.23/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.51  thf(t35_relset_1, conjecture,
% 0.23/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.51     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.23/0.51       ( m1_subset_1 @
% 0.23/0.51         ( k6_relset_1 @ C @ A @ B @ D ) @ 
% 0.23/0.51         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 0.23/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.51    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.51        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.23/0.51          ( m1_subset_1 @
% 0.23/0.51            ( k6_relset_1 @ C @ A @ B @ D ) @ 
% 0.23/0.51            ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )),
% 0.23/0.51    inference('cnf.neg', [status(esa)], [t35_relset_1])).
% 0.23/0.51  thf('0', plain,
% 0.23/0.51      (~ (m1_subset_1 @ (k6_relset_1 @ sk_C @ sk_A @ sk_B @ sk_D) @ 
% 0.23/0.51          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('1', plain,
% 0.23/0.51      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf(redefinition_k6_relset_1, axiom,
% 0.23/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.51     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.51       ( ( k6_relset_1 @ A @ B @ C @ D ) = ( k8_relat_1 @ C @ D ) ) ))).
% 0.23/0.51  thf('2', plain,
% 0.23/0.51      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.23/0.51         (((k6_relset_1 @ X18 @ X19 @ X16 @ X17) = (k8_relat_1 @ X16 @ X17))
% 0.23/0.51          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.23/0.51      inference('cnf', [status(esa)], [redefinition_k6_relset_1])).
% 0.23/0.51  thf('3', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         ((k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D) = (k8_relat_1 @ X0 @ sk_D))),
% 0.23/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.51  thf('4', plain,
% 0.23/0.51      (~ (m1_subset_1 @ (k8_relat_1 @ sk_B @ sk_D) @ 
% 0.23/0.51          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.23/0.51      inference('demod', [status(thm)], ['0', '3'])).
% 0.23/0.51  thf(t116_relat_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( v1_relat_1 @ B ) =>
% 0.23/0.51       ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ A ) ))).
% 0.23/0.51  thf('5', plain,
% 0.23/0.51      (![X4 : $i, X5 : $i]:
% 0.23/0.51         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X4 @ X5)) @ X4)
% 0.23/0.51          | ~ (v1_relat_1 @ X5))),
% 0.23/0.51      inference('cnf', [status(esa)], [t116_relat_1])).
% 0.23/0.51  thf('6', plain,
% 0.23/0.51      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf(dt_k6_relset_1, axiom,
% 0.23/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.51     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.51       ( m1_subset_1 @
% 0.23/0.51         ( k6_relset_1 @ A @ B @ C @ D ) @ 
% 0.23/0.51         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ))).
% 0.23/0.51  thf('7', plain,
% 0.23/0.51      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.23/0.51         ((m1_subset_1 @ (k6_relset_1 @ X12 @ X13 @ X14 @ X15) @ 
% 0.23/0.51           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.23/0.51          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.23/0.51      inference('cnf', [status(esa)], [dt_k6_relset_1])).
% 0.23/0.51  thf('8', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (m1_subset_1 @ (k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D) @ 
% 0.23/0.51          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.23/0.51  thf(cc2_relset_1, axiom,
% 0.23/0.51    (![A:$i,B:$i,C:$i]:
% 0.23/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.51       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.23/0.51  thf('9', plain,
% 0.23/0.51      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.23/0.51         ((v4_relat_1 @ X9 @ X10)
% 0.23/0.51          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.23/0.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.23/0.51  thf('10', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (v4_relat_1 @ (k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D) @ sk_C)),
% 0.23/0.51      inference('sup-', [status(thm)], ['8', '9'])).
% 0.23/0.51  thf(d18_relat_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( v1_relat_1 @ B ) =>
% 0.23/0.51       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.23/0.51  thf('11', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         (~ (v4_relat_1 @ X0 @ X1)
% 0.23/0.51          | (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.23/0.51          | ~ (v1_relat_1 @ X0))),
% 0.23/0.51      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.23/0.51  thf('12', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (~ (v1_relat_1 @ (k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D))
% 0.23/0.51          | (r1_tarski @ 
% 0.23/0.51             (k1_relat_1 @ (k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D)) @ sk_C))),
% 0.23/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.23/0.51  thf('13', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (m1_subset_1 @ (k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D) @ 
% 0.23/0.51          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.23/0.51  thf(cc1_relset_1, axiom,
% 0.23/0.51    (![A:$i,B:$i,C:$i]:
% 0.23/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.51       ( v1_relat_1 @ C ) ))).
% 0.23/0.51  thf('14', plain,
% 0.23/0.51      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.23/0.51         ((v1_relat_1 @ X6)
% 0.23/0.51          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.23/0.51      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.23/0.51  thf('15', plain,
% 0.23/0.51      (![X0 : $i]: (v1_relat_1 @ (k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D))),
% 0.23/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.23/0.51  thf('16', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (r1_tarski @ (k1_relat_1 @ (k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D)) @ 
% 0.23/0.51          sk_C)),
% 0.23/0.51      inference('demod', [status(thm)], ['12', '15'])).
% 0.23/0.51  thf(t11_relset_1, axiom,
% 0.23/0.51    (![A:$i,B:$i,C:$i]:
% 0.23/0.51     ( ( v1_relat_1 @ C ) =>
% 0.23/0.51       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.23/0.51           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.23/0.51         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.23/0.51  thf('17', plain,
% 0.23/0.51      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.23/0.51         (~ (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 0.23/0.51          | ~ (r1_tarski @ (k2_relat_1 @ X20) @ X22)
% 0.23/0.51          | (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.23/0.51          | ~ (v1_relat_1 @ X20))),
% 0.23/0.51      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.23/0.51  thf('18', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         (~ (v1_relat_1 @ (k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D))
% 0.23/0.51          | (m1_subset_1 @ (k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D) @ 
% 0.23/0.51             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 0.23/0.51          | ~ (r1_tarski @ 
% 0.23/0.51               (k2_relat_1 @ (k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D)) @ X1))),
% 0.23/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.23/0.51  thf('19', plain,
% 0.23/0.51      (![X0 : $i]: (v1_relat_1 @ (k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D))),
% 0.23/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.23/0.51  thf('20', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         ((m1_subset_1 @ (k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D) @ 
% 0.23/0.51           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 0.23/0.51          | ~ (r1_tarski @ 
% 0.23/0.51               (k2_relat_1 @ (k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D)) @ X1))),
% 0.23/0.51      inference('demod', [status(thm)], ['18', '19'])).
% 0.23/0.51  thf('21', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         ((k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D) = (k8_relat_1 @ X0 @ sk_D))),
% 0.23/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.51  thf('22', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         ((k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D) = (k8_relat_1 @ X0 @ sk_D))),
% 0.23/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.51  thf('23', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         ((m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 0.23/0.51           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 0.23/0.51          | ~ (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ X1))),
% 0.23/0.51      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.23/0.51  thf('24', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (~ (v1_relat_1 @ sk_D)
% 0.23/0.51          | (m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 0.23/0.51             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X0))))),
% 0.23/0.51      inference('sup-', [status(thm)], ['5', '23'])).
% 0.23/0.51  thf('25', plain,
% 0.23/0.51      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('26', plain,
% 0.23/0.51      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.23/0.51         ((v1_relat_1 @ X6)
% 0.23/0.51          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.23/0.51      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.23/0.51  thf('27', plain, ((v1_relat_1 @ sk_D)),
% 0.23/0.51      inference('sup-', [status(thm)], ['25', '26'])).
% 0.23/0.51  thf('28', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 0.23/0.51          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X0)))),
% 0.23/0.51      inference('demod', [status(thm)], ['24', '27'])).
% 0.23/0.51  thf('29', plain, ($false), inference('demod', [status(thm)], ['4', '28'])).
% 0.23/0.51  
% 0.23/0.51  % SZS output end Refutation
% 0.23/0.51  
% 0.23/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
