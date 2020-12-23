%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EzcHE7M3T8

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:29 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   69 (  87 expanded)
%              Number of leaves         :   29 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :  415 ( 550 expanded)
%              Number of equality atoms :   30 (  42 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X5: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('4',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['2','3'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( r1_tarski @ X3 @ X1 )
      | ( X2
       != ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('6',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X3 @ X1 )
      | ~ ( r2_hidden @ X3 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['4','6'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('8',plain,(
    ! [X9: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('9',plain,(
    ! [X25: $i] :
      ( ( k6_partfun1 @ X25 )
      = ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('10',plain,(
    ! [X9: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X9 ) )
      = X9 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X12 @ ( k2_relat_1 @ X13 ) )
      | ( ( k9_relat_1 @ X13 @ ( k10_relat_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('13',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('14',plain,(
    ! [X25: $i] :
      ( ( k6_partfun1 @ X25 )
      = ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('15',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X10 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X11: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('17',plain,(
    ! [X25: $i] :
      ( ( k6_partfun1 @ X25 )
      = ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('18',plain,(
    ! [X11: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X11 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['12','15','18'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('20',plain,(
    ! [X24: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('21',plain,(
    ! [X25: $i] :
      ( ( k6_partfun1 @ X25 )
      = ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('22',plain,(
    ! [X24: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(dt_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('23',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( m1_subset_1 @ ( k8_relset_1 @ X17 @ X18 @ X16 @ X19 ) @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relset_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X24: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('26',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( ( k8_relset_1 @ X21 @ X22 @ X20 @ X23 )
        = ( k10_relat_1 @ X20 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','27'])).

thf(t162_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B )
        = B ) ) )).

thf('29',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X15 ) @ X14 )
        = X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t162_funct_1])).

thf('30',plain,(
    ! [X25: $i] :
      ( ( k6_partfun1 @ X25 )
      = ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('31',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k9_relat_1 @ ( k6_partfun1 @ X15 ) @ X14 )
        = X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
      = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 )
        = X1 ) ) ),
    inference(demod,[status(thm)],['19','32'])).

thf('34',plain,
    ( ( k10_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['7','33'])).

thf('35',plain,(
    ( k8_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('37',plain,(
    ( k10_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['34','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EzcHE7M3T8
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:13:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 36 iterations in 0.019s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.19/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.46  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.19/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.46  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.19/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.46  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.19/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.46  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.19/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(t171_funct_2, conjecture,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.46       ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i,B:$i]:
% 0.19/0.46        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.46          ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t171_funct_2])).
% 0.19/0.46  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(t2_subset, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( m1_subset_1 @ A @ B ) =>
% 0.19/0.46       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.19/0.46  thf('1', plain,
% 0.19/0.46      (![X6 : $i, X7 : $i]:
% 0.19/0.46         ((r2_hidden @ X6 @ X7)
% 0.19/0.46          | (v1_xboole_0 @ X7)
% 0.19/0.46          | ~ (m1_subset_1 @ X6 @ X7))),
% 0.19/0.46      inference('cnf', [status(esa)], [t2_subset])).
% 0.19/0.46  thf('2', plain,
% 0.19/0.46      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.19/0.46        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.46  thf(fc1_subset_1, axiom,
% 0.19/0.46    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.19/0.46  thf('3', plain, (![X5 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 0.19/0.46      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.19/0.46  thf('4', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.46      inference('clc', [status(thm)], ['2', '3'])).
% 0.19/0.46  thf(d1_zfmisc_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.19/0.46       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.19/0.46  thf('5', plain,
% 0.19/0.46      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.46         (~ (r2_hidden @ X3 @ X2)
% 0.19/0.46          | (r1_tarski @ X3 @ X1)
% 0.19/0.46          | ((X2) != (k1_zfmisc_1 @ X1)))),
% 0.19/0.46      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.19/0.46  thf('6', plain,
% 0.19/0.46      (![X1 : $i, X3 : $i]:
% 0.19/0.46         ((r1_tarski @ X3 @ X1) | ~ (r2_hidden @ X3 @ (k1_zfmisc_1 @ X1)))),
% 0.19/0.46      inference('simplify', [status(thm)], ['5'])).
% 0.19/0.46  thf('7', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.19/0.46      inference('sup-', [status(thm)], ['4', '6'])).
% 0.19/0.46  thf(t71_relat_1, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.19/0.46       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.19/0.46  thf('8', plain, (![X9 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 0.19/0.46      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.46  thf(redefinition_k6_partfun1, axiom,
% 0.19/0.46    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.19/0.46  thf('9', plain, (![X25 : $i]: ((k6_partfun1 @ X25) = (k6_relat_1 @ X25))),
% 0.19/0.46      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.19/0.46  thf('10', plain, (![X9 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X9)) = (X9))),
% 0.19/0.46      inference('demod', [status(thm)], ['8', '9'])).
% 0.19/0.46  thf(t147_funct_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.46       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.19/0.46         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.19/0.46  thf('11', plain,
% 0.19/0.46      (![X12 : $i, X13 : $i]:
% 0.19/0.46         (~ (r1_tarski @ X12 @ (k2_relat_1 @ X13))
% 0.19/0.46          | ((k9_relat_1 @ X13 @ (k10_relat_1 @ X13 @ X12)) = (X12))
% 0.19/0.46          | ~ (v1_funct_1 @ X13)
% 0.19/0.46          | ~ (v1_relat_1 @ X13))),
% 0.19/0.46      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.19/0.46  thf('12', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         (~ (r1_tarski @ X1 @ X0)
% 0.19/0.46          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 0.19/0.46          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 0.19/0.46          | ((k9_relat_1 @ (k6_partfun1 @ X0) @ 
% 0.19/0.46              (k10_relat_1 @ (k6_partfun1 @ X0) @ X1)) = (X1)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.46  thf(fc3_funct_1, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.19/0.46       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.19/0.46  thf('13', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 0.19/0.46      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.46  thf('14', plain, (![X25 : $i]: ((k6_partfun1 @ X25) = (k6_relat_1 @ X25))),
% 0.19/0.46      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.19/0.46  thf('15', plain, (![X10 : $i]: (v1_relat_1 @ (k6_partfun1 @ X10))),
% 0.19/0.46      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.46  thf('16', plain, (![X11 : $i]: (v1_funct_1 @ (k6_relat_1 @ X11))),
% 0.19/0.46      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.46  thf('17', plain, (![X25 : $i]: ((k6_partfun1 @ X25) = (k6_relat_1 @ X25))),
% 0.19/0.46      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.19/0.46  thf('18', plain, (![X11 : $i]: (v1_funct_1 @ (k6_partfun1 @ X11))),
% 0.19/0.46      inference('demod', [status(thm)], ['16', '17'])).
% 0.19/0.46  thf('19', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         (~ (r1_tarski @ X1 @ X0)
% 0.19/0.46          | ((k9_relat_1 @ (k6_partfun1 @ X0) @ 
% 0.19/0.46              (k10_relat_1 @ (k6_partfun1 @ X0) @ X1)) = (X1)))),
% 0.19/0.46      inference('demod', [status(thm)], ['12', '15', '18'])).
% 0.19/0.46  thf(t29_relset_1, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( m1_subset_1 @
% 0.19/0.46       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.19/0.46  thf('20', plain,
% 0.19/0.46      (![X24 : $i]:
% 0.19/0.46         (m1_subset_1 @ (k6_relat_1 @ X24) @ 
% 0.19/0.46          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))),
% 0.19/0.46      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.19/0.46  thf('21', plain, (![X25 : $i]: ((k6_partfun1 @ X25) = (k6_relat_1 @ X25))),
% 0.19/0.46      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.19/0.46  thf('22', plain,
% 0.19/0.46      (![X24 : $i]:
% 0.19/0.46         (m1_subset_1 @ (k6_partfun1 @ X24) @ 
% 0.19/0.46          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))),
% 0.19/0.46      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.46  thf(dt_k8_relset_1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.46       ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.19/0.46  thf('23', plain,
% 0.19/0.46      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.19/0.46         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.19/0.46          | (m1_subset_1 @ (k8_relset_1 @ X17 @ X18 @ X16 @ X19) @ 
% 0.19/0.46             (k1_zfmisc_1 @ X17)))),
% 0.19/0.46      inference('cnf', [status(esa)], [dt_k8_relset_1])).
% 0.19/0.46  thf('24', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         (m1_subset_1 @ (k8_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1) @ 
% 0.19/0.46          (k1_zfmisc_1 @ X0))),
% 0.19/0.46      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.46  thf('25', plain,
% 0.19/0.46      (![X24 : $i]:
% 0.19/0.46         (m1_subset_1 @ (k6_partfun1 @ X24) @ 
% 0.19/0.46          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))),
% 0.19/0.46      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.46  thf(redefinition_k8_relset_1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.46       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.19/0.46  thf('26', plain,
% 0.19/0.46      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.19/0.46         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.19/0.46          | ((k8_relset_1 @ X21 @ X22 @ X20 @ X23) = (k10_relat_1 @ X20 @ X23)))),
% 0.19/0.46      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.19/0.46  thf('27', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         ((k8_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 0.19/0.46           = (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.19/0.46      inference('sup-', [status(thm)], ['25', '26'])).
% 0.19/0.46  thf('28', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         (m1_subset_1 @ (k10_relat_1 @ (k6_partfun1 @ X0) @ X1) @ 
% 0.19/0.46          (k1_zfmisc_1 @ X0))),
% 0.19/0.46      inference('demod', [status(thm)], ['24', '27'])).
% 0.19/0.46  thf(t162_funct_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.46       ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ))).
% 0.19/0.46  thf('29', plain,
% 0.19/0.46      (![X14 : $i, X15 : $i]:
% 0.19/0.46         (((k9_relat_1 @ (k6_relat_1 @ X15) @ X14) = (X14))
% 0.19/0.46          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.19/0.46      inference('cnf', [status(esa)], [t162_funct_1])).
% 0.19/0.46  thf('30', plain, (![X25 : $i]: ((k6_partfun1 @ X25) = (k6_relat_1 @ X25))),
% 0.19/0.46      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.19/0.46  thf('31', plain,
% 0.19/0.46      (![X14 : $i, X15 : $i]:
% 0.19/0.46         (((k9_relat_1 @ (k6_partfun1 @ X15) @ X14) = (X14))
% 0.19/0.46          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.19/0.46      inference('demod', [status(thm)], ['29', '30'])).
% 0.19/0.46  thf('32', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         ((k9_relat_1 @ (k6_partfun1 @ X0) @ 
% 0.19/0.46           (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 0.19/0.46           = (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.19/0.46      inference('sup-', [status(thm)], ['28', '31'])).
% 0.19/0.46  thf('33', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         (~ (r1_tarski @ X1 @ X0)
% 0.19/0.46          | ((k10_relat_1 @ (k6_partfun1 @ X0) @ X1) = (X1)))),
% 0.19/0.46      inference('demod', [status(thm)], ['19', '32'])).
% 0.19/0.46  thf('34', plain, (((k10_relat_1 @ (k6_partfun1 @ sk_A) @ sk_B) = (sk_B))),
% 0.19/0.46      inference('sup-', [status(thm)], ['7', '33'])).
% 0.19/0.46  thf('35', plain,
% 0.19/0.46      (((k8_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ sk_B) != (sk_B))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('36', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         ((k8_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 0.19/0.46           = (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.19/0.46      inference('sup-', [status(thm)], ['25', '26'])).
% 0.19/0.46  thf('37', plain, (((k10_relat_1 @ (k6_partfun1 @ sk_A) @ sk_B) != (sk_B))),
% 0.19/0.46      inference('demod', [status(thm)], ['35', '36'])).
% 0.19/0.46  thf('38', plain, ($false),
% 0.19/0.46      inference('simplify_reflect-', [status(thm)], ['34', '37'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
