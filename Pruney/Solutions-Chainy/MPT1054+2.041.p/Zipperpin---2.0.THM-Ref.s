%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wUVueqkSdX

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   60 (  78 expanded)
%              Number of leaves         :   25 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :  369 ( 504 expanded)
%              Number of equality atoms :   28 (  40 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('2',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('3',plain,(
    ! [X4: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('4',plain,(
    ! [X20: $i] :
      ( ( k6_partfun1 @ X20 )
      = ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('5',plain,(
    ! [X4: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X7 @ ( k2_relat_1 @ X8 ) )
      | ( ( k9_relat_1 @ X8 @ ( k10_relat_1 @ X8 @ X7 ) )
        = X7 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X5: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('9',plain,(
    ! [X20: $i] :
      ( ( k6_partfun1 @ X20 )
      = ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('10',plain,(
    ! [X5: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X5 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X6: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('12',plain,(
    ! [X20: $i] :
      ( ( k6_partfun1 @ X20 )
      = ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('13',plain,(
    ! [X6: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X6 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['7','10','13'])).

thf('15',plain,
    ( ( k9_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k10_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['2','14'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('16',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('17',plain,(
    ! [X20: $i] :
      ( ( k6_partfun1 @ X20 )
      = ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('18',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(dt_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('19',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( m1_subset_1 @ ( k8_relset_1 @ X12 @ X13 @ X11 @ X14 ) @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relset_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('22',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( ( k8_relset_1 @ X16 @ X17 @ X15 @ X18 )
        = ( k10_relat_1 @ X15 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf(t162_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B )
        = B ) ) )).

thf('25',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X10 ) @ X9 )
        = X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t162_funct_1])).

thf('26',plain,(
    ! [X20: $i] :
      ( ( k6_partfun1 @ X20 )
      = ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('27',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k9_relat_1 @ ( k6_partfun1 @ X10 ) @ X9 )
        = X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
      = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,
    ( ( k10_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['15','28'])).

thf('30',plain,(
    ( k8_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('32',plain,(
    ( k10_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['29','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wUVueqkSdX
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:10:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.44  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.44  % Solved by: fo/fo7.sh
% 0.20/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.44  % done 34 iterations in 0.019s
% 0.20/0.44  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.44  % SZS output start Refutation
% 0.20/0.44  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.44  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.44  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.44  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.44  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.44  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.44  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.44  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.20/0.44  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.44  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.44  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.44  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.44  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.44  thf(t171_funct_2, conjecture,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.44       ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ))).
% 0.20/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.44    (~( ![A:$i,B:$i]:
% 0.20/0.44        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.44          ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ) )),
% 0.20/0.44    inference('cnf.neg', [status(esa)], [t171_funct_2])).
% 0.20/0.44  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf(t3_subset, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.44  thf('1', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i]:
% 0.20/0.44         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.20/0.44      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.44  thf('2', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.20/0.44      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.44  thf(t71_relat_1, axiom,
% 0.20/0.44    (![A:$i]:
% 0.20/0.44     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.20/0.44       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.44  thf('3', plain, (![X4 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X4)) = (X4))),
% 0.20/0.44      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.44  thf(redefinition_k6_partfun1, axiom,
% 0.20/0.44    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.20/0.44  thf('4', plain, (![X20 : $i]: ((k6_partfun1 @ X20) = (k6_relat_1 @ X20))),
% 0.20/0.44      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.44  thf('5', plain, (![X4 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 0.20/0.44      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.44  thf(t147_funct_1, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.44       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.20/0.44         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.20/0.44  thf('6', plain,
% 0.20/0.44      (![X7 : $i, X8 : $i]:
% 0.20/0.44         (~ (r1_tarski @ X7 @ (k2_relat_1 @ X8))
% 0.20/0.44          | ((k9_relat_1 @ X8 @ (k10_relat_1 @ X8 @ X7)) = (X7))
% 0.20/0.44          | ~ (v1_funct_1 @ X8)
% 0.20/0.44          | ~ (v1_relat_1 @ X8))),
% 0.20/0.44      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.20/0.44  thf('7', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i]:
% 0.20/0.44         (~ (r1_tarski @ X1 @ X0)
% 0.20/0.44          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 0.20/0.44          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 0.20/0.44          | ((k9_relat_1 @ (k6_partfun1 @ X0) @ 
% 0.20/0.44              (k10_relat_1 @ (k6_partfun1 @ X0) @ X1)) = (X1)))),
% 0.20/0.44      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.44  thf(fc3_funct_1, axiom,
% 0.20/0.44    (![A:$i]:
% 0.20/0.44     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.20/0.44       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.20/0.44  thf('8', plain, (![X5 : $i]: (v1_relat_1 @ (k6_relat_1 @ X5))),
% 0.20/0.44      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.44  thf('9', plain, (![X20 : $i]: ((k6_partfun1 @ X20) = (k6_relat_1 @ X20))),
% 0.20/0.44      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.44  thf('10', plain, (![X5 : $i]: (v1_relat_1 @ (k6_partfun1 @ X5))),
% 0.20/0.44      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.44  thf('11', plain, (![X6 : $i]: (v1_funct_1 @ (k6_relat_1 @ X6))),
% 0.20/0.44      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.44  thf('12', plain, (![X20 : $i]: ((k6_partfun1 @ X20) = (k6_relat_1 @ X20))),
% 0.20/0.44      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.44  thf('13', plain, (![X6 : $i]: (v1_funct_1 @ (k6_partfun1 @ X6))),
% 0.20/0.44      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.44  thf('14', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i]:
% 0.20/0.44         (~ (r1_tarski @ X1 @ X0)
% 0.20/0.44          | ((k9_relat_1 @ (k6_partfun1 @ X0) @ 
% 0.20/0.44              (k10_relat_1 @ (k6_partfun1 @ X0) @ X1)) = (X1)))),
% 0.20/0.44      inference('demod', [status(thm)], ['7', '10', '13'])).
% 0.20/0.44  thf('15', plain,
% 0.20/0.44      (((k9_relat_1 @ (k6_partfun1 @ sk_A) @ 
% 0.20/0.44         (k10_relat_1 @ (k6_partfun1 @ sk_A) @ sk_B)) = (sk_B))),
% 0.20/0.44      inference('sup-', [status(thm)], ['2', '14'])).
% 0.20/0.44  thf(t29_relset_1, axiom,
% 0.20/0.44    (![A:$i]:
% 0.20/0.44     ( m1_subset_1 @
% 0.20/0.44       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.20/0.44  thf('16', plain,
% 0.20/0.44      (![X19 : $i]:
% 0.20/0.44         (m1_subset_1 @ (k6_relat_1 @ X19) @ 
% 0.20/0.44          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))),
% 0.20/0.44      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.20/0.44  thf('17', plain, (![X20 : $i]: ((k6_partfun1 @ X20) = (k6_relat_1 @ X20))),
% 0.20/0.44      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.44  thf('18', plain,
% 0.20/0.44      (![X19 : $i]:
% 0.20/0.44         (m1_subset_1 @ (k6_partfun1 @ X19) @ 
% 0.20/0.44          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))),
% 0.20/0.44      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.44  thf(dt_k8_relset_1, axiom,
% 0.20/0.44    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.44     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.44       ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.44  thf('19', plain,
% 0.20/0.44      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.44         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.20/0.44          | (m1_subset_1 @ (k8_relset_1 @ X12 @ X13 @ X11 @ X14) @ 
% 0.20/0.44             (k1_zfmisc_1 @ X12)))),
% 0.20/0.44      inference('cnf', [status(esa)], [dt_k8_relset_1])).
% 0.20/0.44  thf('20', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i]:
% 0.20/0.44         (m1_subset_1 @ (k8_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1) @ 
% 0.20/0.44          (k1_zfmisc_1 @ X0))),
% 0.20/0.44      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.44  thf('21', plain,
% 0.20/0.44      (![X19 : $i]:
% 0.20/0.44         (m1_subset_1 @ (k6_partfun1 @ X19) @ 
% 0.20/0.44          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))),
% 0.20/0.44      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.44  thf(redefinition_k8_relset_1, axiom,
% 0.20/0.44    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.44     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.44       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.20/0.44  thf('22', plain,
% 0.20/0.44      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.44         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.20/0.44          | ((k8_relset_1 @ X16 @ X17 @ X15 @ X18) = (k10_relat_1 @ X15 @ X18)))),
% 0.20/0.44      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.20/0.44  thf('23', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i]:
% 0.20/0.44         ((k8_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 0.20/0.44           = (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.20/0.44      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.44  thf('24', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i]:
% 0.20/0.44         (m1_subset_1 @ (k10_relat_1 @ (k6_partfun1 @ X0) @ X1) @ 
% 0.20/0.44          (k1_zfmisc_1 @ X0))),
% 0.20/0.44      inference('demod', [status(thm)], ['20', '23'])).
% 0.20/0.44  thf(t162_funct_1, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.44       ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ))).
% 0.20/0.44  thf('25', plain,
% 0.20/0.44      (![X9 : $i, X10 : $i]:
% 0.20/0.44         (((k9_relat_1 @ (k6_relat_1 @ X10) @ X9) = (X9))
% 0.20/0.44          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.20/0.44      inference('cnf', [status(esa)], [t162_funct_1])).
% 0.20/0.44  thf('26', plain, (![X20 : $i]: ((k6_partfun1 @ X20) = (k6_relat_1 @ X20))),
% 0.20/0.44      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.44  thf('27', plain,
% 0.20/0.44      (![X9 : $i, X10 : $i]:
% 0.20/0.44         (((k9_relat_1 @ (k6_partfun1 @ X10) @ X9) = (X9))
% 0.20/0.44          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.20/0.44      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.44  thf('28', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i]:
% 0.20/0.44         ((k9_relat_1 @ (k6_partfun1 @ X0) @ 
% 0.20/0.44           (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 0.20/0.44           = (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.20/0.44      inference('sup-', [status(thm)], ['24', '27'])).
% 0.20/0.44  thf('29', plain, (((k10_relat_1 @ (k6_partfun1 @ sk_A) @ sk_B) = (sk_B))),
% 0.20/0.44      inference('demod', [status(thm)], ['15', '28'])).
% 0.20/0.44  thf('30', plain,
% 0.20/0.44      (((k8_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ sk_B) != (sk_B))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('31', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i]:
% 0.20/0.44         ((k8_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 0.20/0.44           = (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.20/0.44      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.44  thf('32', plain, (((k10_relat_1 @ (k6_partfun1 @ sk_A) @ sk_B) != (sk_B))),
% 0.20/0.44      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.44  thf('33', plain, ($false),
% 0.20/0.44      inference('simplify_reflect-', [status(thm)], ['29', '32'])).
% 0.20/0.44  
% 0.20/0.44  % SZS output end Refutation
% 0.20/0.44  
% 0.20/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
