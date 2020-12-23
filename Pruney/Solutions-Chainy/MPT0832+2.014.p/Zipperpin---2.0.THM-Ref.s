%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZSRpf937d7

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:30 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   68 (  86 expanded)
%              Number of leaves         :   29 (  37 expanded)
%              Depth                    :   15
%              Number of atoms          :  457 ( 693 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k6_relset_1_type,type,(
    k6_relset_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ~ ( m1_subset_1 @ ( k6_relset_1 @ sk_C_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k6_relset_1 @ A @ B @ C @ D )
        = ( k8_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( ( k6_relset_1 @ X28 @ X29 @ X26 @ X27 )
        = ( k8_relat_1 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k6_relset_1 @ sk_C_1 @ sk_A @ X0 @ sk_D )
      = ( k8_relat_1 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( m1_subset_1 @ ( k8_relat_1 @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf(t116_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ A ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X13 @ X14 ) ) @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t116_relat_1])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X20 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('9',plain,(
    m1_subset_1 @ ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_D ) @ ( k1_zfmisc_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('12',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_D ) @ ( k1_zfmisc_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['9','12'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('15',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_C_1 ) )
    | ( r2_hidden @ ( k1_relat_1 @ sk_D ) @ ( k1_zfmisc_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('16',plain,(
    ! [X8: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('17',plain,(
    r2_hidden @ ( k1_relat_1 @ sk_D ) @ ( k1_zfmisc_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['15','16'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('18',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r1_tarski @ X6 @ X4 )
      | ( X5
       != ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('19',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['17','19'])).

thf(l29_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ B ) ) ) )).

thf('21',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k8_relat_1 @ X15 @ X16 ) ) @ ( k1_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[l29_wellord1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('26',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('27',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['24','27'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('29',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X30 ) @ X31 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X30 ) @ X32 )
      | ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) )
      | ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['6','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['25','26'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['25','26'])).

thf('36',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['4','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZSRpf937d7
% 0.14/0.37  % Computer   : n022.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 19:03:11 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.24/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.53  % Solved by: fo/fo7.sh
% 0.24/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.53  % done 85 iterations in 0.060s
% 0.24/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.53  % SZS output start Refutation
% 0.24/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.24/0.53  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.24/0.53  thf(k6_relset_1_type, type, k6_relset_1: $i > $i > $i > $i > $i).
% 0.24/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.24/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.24/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.24/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.24/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.24/0.53  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.24/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.24/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.53  thf(t35_relset_1, conjecture,
% 0.24/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.53     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.24/0.53       ( m1_subset_1 @
% 0.24/0.53         ( k6_relset_1 @ C @ A @ B @ D ) @ 
% 0.24/0.53         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 0.24/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.53    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.53        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.24/0.53          ( m1_subset_1 @
% 0.24/0.53            ( k6_relset_1 @ C @ A @ B @ D ) @ 
% 0.24/0.53            ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )),
% 0.24/0.53    inference('cnf.neg', [status(esa)], [t35_relset_1])).
% 0.24/0.53  thf('0', plain,
% 0.24/0.53      (~ (m1_subset_1 @ (k6_relset_1 @ sk_C_1 @ sk_A @ sk_B @ sk_D) @ 
% 0.24/0.53          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('1', plain,
% 0.24/0.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf(redefinition_k6_relset_1, axiom,
% 0.24/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.53     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.24/0.53       ( ( k6_relset_1 @ A @ B @ C @ D ) = ( k8_relat_1 @ C @ D ) ) ))).
% 0.24/0.53  thf('2', plain,
% 0.24/0.53      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.24/0.53         (((k6_relset_1 @ X28 @ X29 @ X26 @ X27) = (k8_relat_1 @ X26 @ X27))
% 0.24/0.53          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.24/0.53      inference('cnf', [status(esa)], [redefinition_k6_relset_1])).
% 0.24/0.53  thf('3', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         ((k6_relset_1 @ sk_C_1 @ sk_A @ X0 @ sk_D) = (k8_relat_1 @ X0 @ sk_D))),
% 0.24/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.24/0.53  thf('4', plain,
% 0.24/0.53      (~ (m1_subset_1 @ (k8_relat_1 @ sk_B @ sk_D) @ 
% 0.24/0.53          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 0.24/0.53      inference('demod', [status(thm)], ['0', '3'])).
% 0.24/0.53  thf(dt_k8_relat_1, axiom,
% 0.24/0.53    (![A:$i,B:$i]:
% 0.24/0.53     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 0.24/0.53  thf('5', plain,
% 0.24/0.53      (![X11 : $i, X12 : $i]:
% 0.24/0.53         ((v1_relat_1 @ (k8_relat_1 @ X11 @ X12)) | ~ (v1_relat_1 @ X12))),
% 0.24/0.53      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.24/0.53  thf(t116_relat_1, axiom,
% 0.24/0.53    (![A:$i,B:$i]:
% 0.24/0.53     ( ( v1_relat_1 @ B ) =>
% 0.24/0.53       ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ A ) ))).
% 0.24/0.53  thf('6', plain,
% 0.24/0.53      (![X13 : $i, X14 : $i]:
% 0.24/0.53         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X13 @ X14)) @ X13)
% 0.24/0.53          | ~ (v1_relat_1 @ X14))),
% 0.24/0.53      inference('cnf', [status(esa)], [t116_relat_1])).
% 0.24/0.53  thf('7', plain,
% 0.24/0.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf(dt_k1_relset_1, axiom,
% 0.24/0.53    (![A:$i,B:$i,C:$i]:
% 0.24/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.24/0.53       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.24/0.53  thf('8', plain,
% 0.24/0.53      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.24/0.53         ((m1_subset_1 @ (k1_relset_1 @ X20 @ X21 @ X22) @ (k1_zfmisc_1 @ X20))
% 0.24/0.53          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.24/0.53      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.24/0.53  thf('9', plain,
% 0.24/0.53      ((m1_subset_1 @ (k1_relset_1 @ sk_C_1 @ sk_A @ sk_D) @ 
% 0.24/0.53        (k1_zfmisc_1 @ sk_C_1))),
% 0.24/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.24/0.53  thf('10', plain,
% 0.24/0.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf(redefinition_k1_relset_1, axiom,
% 0.24/0.53    (![A:$i,B:$i,C:$i]:
% 0.24/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.24/0.53       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.24/0.53  thf('11', plain,
% 0.24/0.53      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.24/0.53         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 0.24/0.53          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.24/0.53      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.24/0.53  thf('12', plain,
% 0.24/0.53      (((k1_relset_1 @ sk_C_1 @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.24/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.24/0.53  thf('13', plain,
% 0.24/0.53      ((m1_subset_1 @ (k1_relat_1 @ sk_D) @ (k1_zfmisc_1 @ sk_C_1))),
% 0.24/0.53      inference('demod', [status(thm)], ['9', '12'])).
% 0.24/0.53  thf(t2_subset, axiom,
% 0.24/0.53    (![A:$i,B:$i]:
% 0.24/0.53     ( ( m1_subset_1 @ A @ B ) =>
% 0.24/0.53       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.24/0.53  thf('14', plain,
% 0.24/0.53      (![X9 : $i, X10 : $i]:
% 0.24/0.53         ((r2_hidden @ X9 @ X10)
% 0.24/0.53          | (v1_xboole_0 @ X10)
% 0.24/0.53          | ~ (m1_subset_1 @ X9 @ X10))),
% 0.24/0.53      inference('cnf', [status(esa)], [t2_subset])).
% 0.24/0.53  thf('15', plain,
% 0.24/0.53      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_C_1))
% 0.24/0.53        | (r2_hidden @ (k1_relat_1 @ sk_D) @ (k1_zfmisc_1 @ sk_C_1)))),
% 0.24/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.24/0.53  thf(fc1_subset_1, axiom,
% 0.24/0.53    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.24/0.53  thf('16', plain, (![X8 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.24/0.53      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.24/0.53  thf('17', plain,
% 0.24/0.53      ((r2_hidden @ (k1_relat_1 @ sk_D) @ (k1_zfmisc_1 @ sk_C_1))),
% 0.24/0.53      inference('clc', [status(thm)], ['15', '16'])).
% 0.24/0.53  thf(d1_zfmisc_1, axiom,
% 0.24/0.53    (![A:$i,B:$i]:
% 0.24/0.53     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.24/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.24/0.53  thf('18', plain,
% 0.24/0.53      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.24/0.53         (~ (r2_hidden @ X6 @ X5)
% 0.24/0.53          | (r1_tarski @ X6 @ X4)
% 0.24/0.53          | ((X5) != (k1_zfmisc_1 @ X4)))),
% 0.24/0.53      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.24/0.53  thf('19', plain,
% 0.24/0.53      (![X4 : $i, X6 : $i]:
% 0.24/0.53         ((r1_tarski @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k1_zfmisc_1 @ X4)))),
% 0.24/0.53      inference('simplify', [status(thm)], ['18'])).
% 0.24/0.53  thf('20', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_C_1)),
% 0.24/0.53      inference('sup-', [status(thm)], ['17', '19'])).
% 0.24/0.53  thf(l29_wellord1, axiom,
% 0.24/0.53    (![A:$i,B:$i]:
% 0.24/0.53     ( ( v1_relat_1 @ B ) =>
% 0.24/0.53       ( r1_tarski @
% 0.24/0.53         ( k1_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ B ) ) ))).
% 0.24/0.53  thf('21', plain,
% 0.24/0.53      (![X15 : $i, X16 : $i]:
% 0.24/0.53         ((r1_tarski @ (k1_relat_1 @ (k8_relat_1 @ X15 @ X16)) @ 
% 0.24/0.53           (k1_relat_1 @ X16))
% 0.24/0.53          | ~ (v1_relat_1 @ X16))),
% 0.24/0.53      inference('cnf', [status(esa)], [l29_wellord1])).
% 0.24/0.53  thf(t1_xboole_1, axiom,
% 0.24/0.53    (![A:$i,B:$i,C:$i]:
% 0.24/0.53     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.24/0.53       ( r1_tarski @ A @ C ) ))).
% 0.24/0.53  thf('22', plain,
% 0.24/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.53         (~ (r1_tarski @ X0 @ X1)
% 0.24/0.53          | ~ (r1_tarski @ X1 @ X2)
% 0.24/0.53          | (r1_tarski @ X0 @ X2))),
% 0.24/0.53      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.24/0.53  thf('23', plain,
% 0.24/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.53         (~ (v1_relat_1 @ X0)
% 0.24/0.53          | (r1_tarski @ (k1_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X2)
% 0.24/0.53          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ X2))),
% 0.24/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.24/0.53  thf('24', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         ((r1_tarski @ (k1_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ sk_C_1)
% 0.24/0.53          | ~ (v1_relat_1 @ sk_D))),
% 0.24/0.53      inference('sup-', [status(thm)], ['20', '23'])).
% 0.24/0.53  thf('25', plain,
% 0.24/0.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf(cc1_relset_1, axiom,
% 0.24/0.53    (![A:$i,B:$i,C:$i]:
% 0.24/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.24/0.53       ( v1_relat_1 @ C ) ))).
% 0.24/0.53  thf('26', plain,
% 0.24/0.53      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.24/0.53         ((v1_relat_1 @ X17)
% 0.24/0.53          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.24/0.53      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.24/0.53  thf('27', plain, ((v1_relat_1 @ sk_D)),
% 0.24/0.53      inference('sup-', [status(thm)], ['25', '26'])).
% 0.24/0.53  thf('28', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         (r1_tarski @ (k1_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ sk_C_1)),
% 0.24/0.53      inference('demod', [status(thm)], ['24', '27'])).
% 0.24/0.53  thf(t11_relset_1, axiom,
% 0.24/0.53    (![A:$i,B:$i,C:$i]:
% 0.24/0.53     ( ( v1_relat_1 @ C ) =>
% 0.24/0.53       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.24/0.53           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.24/0.53         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.24/0.53  thf('29', plain,
% 0.24/0.53      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.24/0.53         (~ (r1_tarski @ (k1_relat_1 @ X30) @ X31)
% 0.24/0.53          | ~ (r1_tarski @ (k2_relat_1 @ X30) @ X32)
% 0.24/0.53          | (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.24/0.53          | ~ (v1_relat_1 @ X30))),
% 0.24/0.53      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.24/0.53  thf('30', plain,
% 0.24/0.53      (![X0 : $i, X1 : $i]:
% 0.24/0.53         (~ (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_D))
% 0.24/0.53          | (m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 0.24/0.53             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 0.24/0.53          | ~ (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X0 @ sk_D)) @ X1))),
% 0.24/0.53      inference('sup-', [status(thm)], ['28', '29'])).
% 0.24/0.53  thf('31', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         (~ (v1_relat_1 @ sk_D)
% 0.24/0.53          | (m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 0.24/0.53             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X0)))
% 0.24/0.53          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_D)))),
% 0.24/0.53      inference('sup-', [status(thm)], ['6', '30'])).
% 0.24/0.53  thf('32', plain, ((v1_relat_1 @ sk_D)),
% 0.24/0.53      inference('sup-', [status(thm)], ['25', '26'])).
% 0.24/0.53  thf('33', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         ((m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 0.24/0.53           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X0)))
% 0.24/0.53          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_D)))),
% 0.24/0.53      inference('demod', [status(thm)], ['31', '32'])).
% 0.24/0.53  thf('34', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         (~ (v1_relat_1 @ sk_D)
% 0.24/0.53          | (m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 0.24/0.53             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X0))))),
% 0.24/0.53      inference('sup-', [status(thm)], ['5', '33'])).
% 0.24/0.53  thf('35', plain, ((v1_relat_1 @ sk_D)),
% 0.24/0.53      inference('sup-', [status(thm)], ['25', '26'])).
% 0.24/0.53  thf('36', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         (m1_subset_1 @ (k8_relat_1 @ X0 @ sk_D) @ 
% 0.24/0.53          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X0)))),
% 0.24/0.53      inference('demod', [status(thm)], ['34', '35'])).
% 0.24/0.53  thf('37', plain, ($false), inference('demod', [status(thm)], ['4', '36'])).
% 0.24/0.53  
% 0.24/0.53  % SZS output end Refutation
% 0.24/0.53  
% 0.38/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
