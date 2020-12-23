%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bWa27kj8YI

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:33 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   62 (  78 expanded)
%              Number of leaves         :   26 (  34 expanded)
%              Depth                    :   12
%              Number of atoms          :  397 ( 575 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_relset_1_type,type,(
    k6_relset_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( ( k6_relset_1 @ X21 @ X22 @ X19 @ X20 )
        = ( k8_relat_1 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X15 @ X16 ) ) @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t116_relat_1])).

thf(t117_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X17 @ X18 ) @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t117_relat_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X5: $i,X7: $i] :
      ( ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k8_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ ( k8_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('11',plain,(
    ! [X2: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k8_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t79_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('17',plain,(
    r1_tarski @ ( k1_zfmisc_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X5: $i,X7: $i] :
      ( ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('19',plain,(
    m1_subset_1 @ ( k1_zfmisc_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( m1_subset_1 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['12','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('24',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('26',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('27',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['22','27'])).

thf(t14_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) )).

thf('29',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X23 ) @ X24 )
      | ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[t14_relset_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['25','26'])).

thf('33',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['4','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bWa27kj8YI
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:14:03 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.37/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.53  % Solved by: fo/fo7.sh
% 0.37/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.53  % done 159 iterations in 0.090s
% 0.37/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.53  % SZS output start Refutation
% 0.37/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.37/0.53  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.37/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.53  thf(k6_relset_1_type, type, k6_relset_1: $i > $i > $i > $i > $i).
% 0.37/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.53  thf(t35_relset_1, conjecture,
% 0.37/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.53     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.37/0.53       ( m1_subset_1 @
% 0.37/0.53         ( k6_relset_1 @ C @ A @ B @ D ) @ 
% 0.37/0.53         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 0.37/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.53    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.53        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.37/0.53          ( m1_subset_1 @
% 0.37/0.53            ( k6_relset_1 @ C @ A @ B @ D ) @ 
% 0.37/0.53            ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )),
% 0.37/0.53    inference('cnf.neg', [status(esa)], [t35_relset_1])).
% 0.37/0.53  thf('0', plain,
% 0.37/0.53      (~ (m1_subset_1 @ (k6_relset_1 @ sk_C @ sk_A @ sk_B @ sk_D) @ 
% 0.37/0.53          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.37/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.53  thf('1', plain,
% 0.37/0.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.37/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.53  thf(redefinition_k6_relset_1, axiom,
% 0.37/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.53     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.53       ( ( k6_relset_1 @ A @ B @ C @ D ) = ( k8_relat_1 @ C @ D ) ) ))).
% 0.37/0.53  thf('2', plain,
% 0.37/0.53      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.37/0.53         (((k6_relset_1 @ X21 @ X22 @ X19 @ X20) = (k8_relat_1 @ X19 @ X20))
% 0.37/0.53          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.37/0.53      inference('cnf', [status(esa)], [redefinition_k6_relset_1])).
% 0.37/0.53  thf('3', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         ((k6_relset_1 @ sk_C @ sk_A @ X0 @ sk_D) = (k8_relat_1 @ X0 @ sk_D))),
% 0.37/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.53  thf('4', plain,
% 0.37/0.53      (~ (m1_subset_1 @ (k8_relat_1 @ sk_B @ sk_D) @ 
% 0.37/0.53          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.37/0.53      inference('demod', [status(thm)], ['0', '3'])).
% 0.37/0.53  thf(t116_relat_1, axiom,
% 0.37/0.53    (![A:$i,B:$i]:
% 0.37/0.53     ( ( v1_relat_1 @ B ) =>
% 0.37/0.53       ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ A ) ))).
% 0.37/0.53  thf('5', plain,
% 0.37/0.53      (![X15 : $i, X16 : $i]:
% 0.37/0.53         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X15 @ X16)) @ X15)
% 0.37/0.53          | ~ (v1_relat_1 @ X16))),
% 0.37/0.53      inference('cnf', [status(esa)], [t116_relat_1])).
% 0.37/0.53  thf(t117_relat_1, axiom,
% 0.37/0.53    (![A:$i,B:$i]:
% 0.37/0.53     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ))).
% 0.37/0.53  thf('6', plain,
% 0.37/0.53      (![X17 : $i, X18 : $i]:
% 0.37/0.53         ((r1_tarski @ (k8_relat_1 @ X17 @ X18) @ X18) | ~ (v1_relat_1 @ X18))),
% 0.37/0.53      inference('cnf', [status(esa)], [t117_relat_1])).
% 0.37/0.53  thf(t3_subset, axiom,
% 0.37/0.53    (![A:$i,B:$i]:
% 0.37/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.53  thf('7', plain,
% 0.37/0.53      (![X5 : $i, X7 : $i]:
% 0.37/0.53         ((m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X7)) | ~ (r1_tarski @ X5 @ X7))),
% 0.37/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.53  thf('8', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i]:
% 0.37/0.53         (~ (v1_relat_1 @ X0)
% 0.37/0.53          | (m1_subset_1 @ (k8_relat_1 @ X1 @ X0) @ (k1_zfmisc_1 @ X0)))),
% 0.37/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.53  thf(t2_subset, axiom,
% 0.37/0.53    (![A:$i,B:$i]:
% 0.37/0.53     ( ( m1_subset_1 @ A @ B ) =>
% 0.37/0.53       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.37/0.53  thf('9', plain,
% 0.37/0.53      (![X3 : $i, X4 : $i]:
% 0.37/0.53         ((r2_hidden @ X3 @ X4)
% 0.37/0.53          | (v1_xboole_0 @ X4)
% 0.37/0.53          | ~ (m1_subset_1 @ X3 @ X4))),
% 0.37/0.53      inference('cnf', [status(esa)], [t2_subset])).
% 0.37/0.53  thf('10', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i]:
% 0.37/0.53         (~ (v1_relat_1 @ X0)
% 0.37/0.53          | (v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.37/0.53          | (r2_hidden @ (k8_relat_1 @ X1 @ X0) @ (k1_zfmisc_1 @ X0)))),
% 0.37/0.53      inference('sup-', [status(thm)], ['8', '9'])).
% 0.37/0.53  thf(fc1_subset_1, axiom,
% 0.37/0.53    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.37/0.53  thf('11', plain, (![X2 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X2))),
% 0.37/0.53      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.37/0.53  thf('12', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i]:
% 0.37/0.53         ((r2_hidden @ (k8_relat_1 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))
% 0.37/0.53          | ~ (v1_relat_1 @ X0))),
% 0.37/0.53      inference('clc', [status(thm)], ['10', '11'])).
% 0.37/0.53  thf('13', plain,
% 0.37/0.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.37/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.53  thf('14', plain,
% 0.37/0.53      (![X5 : $i, X6 : $i]:
% 0.37/0.53         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.37/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.53  thf('15', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_C @ sk_A))),
% 0.37/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.53  thf(t79_zfmisc_1, axiom,
% 0.37/0.53    (![A:$i,B:$i]:
% 0.37/0.53     ( ( r1_tarski @ A @ B ) =>
% 0.37/0.53       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.37/0.53  thf('16', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i]:
% 0.37/0.53         ((r1_tarski @ (k1_zfmisc_1 @ X0) @ (k1_zfmisc_1 @ X1))
% 0.37/0.53          | ~ (r1_tarski @ X0 @ X1))),
% 0.37/0.53      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 0.37/0.53  thf('17', plain,
% 0.37/0.53      ((r1_tarski @ (k1_zfmisc_1 @ sk_D) @ 
% 0.37/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.37/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.37/0.53  thf('18', plain,
% 0.37/0.53      (![X5 : $i, X7 : $i]:
% 0.37/0.53         ((m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X7)) | ~ (r1_tarski @ X5 @ X7))),
% 0.37/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.53  thf('19', plain,
% 0.37/0.53      ((m1_subset_1 @ (k1_zfmisc_1 @ sk_D) @ 
% 0.37/0.53        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A))))),
% 0.37/0.53      inference('sup-', [status(thm)], ['17', '18'])).
% 0.37/0.53  thf(t4_subset, axiom,
% 0.37/0.53    (![A:$i,B:$i,C:$i]:
% 0.37/0.53     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.37/0.53       ( m1_subset_1 @ A @ C ) ))).
% 0.37/0.53  thf('20', plain,
% 0.37/0.53      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.37/0.53         (~ (r2_hidden @ X8 @ X9)
% 0.37/0.53          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.37/0.53          | (m1_subset_1 @ X8 @ X10))),
% 0.37/0.53      inference('cnf', [status(esa)], [t4_subset])).
% 0.37/0.53  thf('21', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))
% 0.37/0.53          | ~ (r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_D)))),
% 0.37/0.53      inference('sup-', [status(thm)], ['19', '20'])).
% 0.37/0.53  thf('22', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         (~ (v1_relat_1 @ sk_D)
% 0.37/0.53          | (m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 0.37/0.53             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A))))),
% 0.37/0.53      inference('sup-', [status(thm)], ['12', '21'])).
% 0.37/0.53  thf('23', plain,
% 0.37/0.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.37/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.53  thf(cc2_relat_1, axiom,
% 0.37/0.53    (![A:$i]:
% 0.37/0.53     ( ( v1_relat_1 @ A ) =>
% 0.37/0.53       ( ![B:$i]:
% 0.37/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.37/0.53  thf('24', plain,
% 0.37/0.53      (![X11 : $i, X12 : $i]:
% 0.37/0.53         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.37/0.53          | (v1_relat_1 @ X11)
% 0.37/0.53          | ~ (v1_relat_1 @ X12))),
% 0.37/0.53      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.37/0.53  thf('25', plain,
% 0.37/0.53      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.37/0.53      inference('sup-', [status(thm)], ['23', '24'])).
% 0.37/0.53  thf(fc6_relat_1, axiom,
% 0.37/0.53    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.37/0.53  thf('26', plain,
% 0.37/0.53      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14))),
% 0.37/0.53      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.37/0.53  thf('27', plain, ((v1_relat_1 @ sk_D)),
% 0.37/0.53      inference('demod', [status(thm)], ['25', '26'])).
% 0.37/0.53  thf('28', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         (m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 0.37/0.53          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.37/0.53      inference('demod', [status(thm)], ['22', '27'])).
% 0.37/0.53  thf(t14_relset_1, axiom,
% 0.37/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.53     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.37/0.53       ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B ) =>
% 0.37/0.53         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ))).
% 0.37/0.53  thf('29', plain,
% 0.37/0.53      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.37/0.53         (~ (r1_tarski @ (k2_relat_1 @ X23) @ X24)
% 0.37/0.53          | (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24)))
% 0.37/0.53          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.37/0.53      inference('cnf', [status(esa)], [t14_relset_1])).
% 0.37/0.53  thf('30', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i]:
% 0.37/0.53         ((m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 0.37/0.53           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 0.37/0.53          | ~ (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ X1))),
% 0.37/0.53      inference('sup-', [status(thm)], ['28', '29'])).
% 0.37/0.53  thf('31', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         (~ (v1_relat_1 @ sk_D)
% 0.37/0.53          | (m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 0.37/0.53             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X0))))),
% 0.37/0.53      inference('sup-', [status(thm)], ['5', '30'])).
% 0.37/0.53  thf('32', plain, ((v1_relat_1 @ sk_D)),
% 0.37/0.53      inference('demod', [status(thm)], ['25', '26'])).
% 0.37/0.53  thf('33', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         (m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 0.37/0.53          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X0)))),
% 0.37/0.53      inference('demod', [status(thm)], ['31', '32'])).
% 0.37/0.53  thf('34', plain, ($false), inference('demod', [status(thm)], ['4', '33'])).
% 0.37/0.53  
% 0.37/0.53  % SZS output end Refutation
% 0.37/0.53  
% 0.37/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
