%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VZHva4JQmi

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:31 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   63 (  76 expanded)
%              Number of leaves         :   26 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :  362 ( 448 expanded)
%              Number of equality atoms :   29 (  39 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

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
    ! [X6: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('4',plain,(
    ! [X19: $i] :
      ( ( k6_partfun1 @ X19 )
      = ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('5',plain,(
    ! [X6: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X6 ) )
      = X6 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X9 @ ( k2_relat_1 @ X10 ) )
      | ( ( k9_relat_1 @ X10 @ ( k10_relat_1 @ X10 @ X9 ) )
        = X9 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
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
    ! [X7: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('9',plain,(
    ! [X19: $i] :
      ( ( k6_partfun1 @ X19 )
      = ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('10',plain,(
    ! [X7: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X7 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X8: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('12',plain,(
    ! [X19: $i] :
      ( ( k6_partfun1 @ X19 )
      = ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('13',plain,(
    ! [X8: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X8 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['7','10','13'])).

thf('15',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('16',plain,(
    ! [X19: $i] :
      ( ( k6_partfun1 @ X19 )
      = ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('17',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X5 ) )
      = X5 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X3 @ X4 ) @ ( k1_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X7: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X7 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t162_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B )
        = B ) ) )).

thf('24',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X12 ) @ X11 )
        = X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t162_funct_1])).

thf('25',plain,(
    ! [X19: $i] :
      ( ( k6_partfun1 @ X19 )
      = ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('26',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k9_relat_1 @ ( k6_partfun1 @ X12 ) @ X11 )
        = X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
      = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 )
        = X1 ) ) ),
    inference(demod,[status(thm)],['14','27'])).

thf('29',plain,
    ( ( k10_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['2','28'])).

thf('30',plain,(
    ( k8_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('31',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('32',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( ( k8_relset_1 @ X14 @ X15 @ X13 @ X16 )
        = ( k10_relat_1 @ X13 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ( k10_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(demod,[status(thm)],['30','33'])).

thf('35',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['29','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VZHva4JQmi
% 0.12/0.32  % Computer   : n014.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 14:18:52 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running portfolio for 600 s
% 0.12/0.32  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.32  % Number of cores: 8
% 0.12/0.32  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.18/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.18/0.46  % Solved by: fo/fo7.sh
% 0.18/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.46  % done 30 iterations in 0.018s
% 0.18/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.18/0.46  % SZS output start Refutation
% 0.18/0.46  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.18/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.18/0.46  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.18/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.18/0.46  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.18/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.18/0.46  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.18/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.18/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.18/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.18/0.46  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.18/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.18/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.18/0.46  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.18/0.46  thf(t171_funct_2, conjecture,
% 0.18/0.46    (![A:$i,B:$i]:
% 0.18/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.18/0.46       ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ))).
% 0.18/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.46    (~( ![A:$i,B:$i]:
% 0.18/0.46        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.18/0.46          ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ) )),
% 0.18/0.46    inference('cnf.neg', [status(esa)], [t171_funct_2])).
% 0.18/0.46  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf(t3_subset, axiom,
% 0.18/0.46    (![A:$i,B:$i]:
% 0.18/0.46     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.18/0.46  thf('1', plain,
% 0.18/0.46      (![X0 : $i, X1 : $i]:
% 0.18/0.46         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.18/0.46      inference('cnf', [status(esa)], [t3_subset])).
% 0.18/0.46  thf('2', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.18/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.18/0.46  thf(t71_relat_1, axiom,
% 0.18/0.46    (![A:$i]:
% 0.18/0.46     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.18/0.46       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.18/0.46  thf('3', plain, (![X6 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X6)) = (X6))),
% 0.18/0.46      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.18/0.46  thf(redefinition_k6_partfun1, axiom,
% 0.18/0.46    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.18/0.46  thf('4', plain, (![X19 : $i]: ((k6_partfun1 @ X19) = (k6_relat_1 @ X19))),
% 0.18/0.46      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.18/0.46  thf('5', plain, (![X6 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X6)) = (X6))),
% 0.18/0.46      inference('demod', [status(thm)], ['3', '4'])).
% 0.18/0.46  thf(t147_funct_1, axiom,
% 0.18/0.46    (![A:$i,B:$i]:
% 0.18/0.46     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.18/0.46       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.18/0.46         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.18/0.46  thf('6', plain,
% 0.18/0.46      (![X9 : $i, X10 : $i]:
% 0.18/0.46         (~ (r1_tarski @ X9 @ (k2_relat_1 @ X10))
% 0.18/0.46          | ((k9_relat_1 @ X10 @ (k10_relat_1 @ X10 @ X9)) = (X9))
% 0.18/0.46          | ~ (v1_funct_1 @ X10)
% 0.18/0.46          | ~ (v1_relat_1 @ X10))),
% 0.18/0.46      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.18/0.46  thf('7', plain,
% 0.18/0.46      (![X0 : $i, X1 : $i]:
% 0.18/0.46         (~ (r1_tarski @ X1 @ X0)
% 0.18/0.46          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 0.18/0.46          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 0.18/0.46          | ((k9_relat_1 @ (k6_partfun1 @ X0) @ 
% 0.18/0.46              (k10_relat_1 @ (k6_partfun1 @ X0) @ X1)) = (X1)))),
% 0.18/0.46      inference('sup-', [status(thm)], ['5', '6'])).
% 0.18/0.46  thf(fc3_funct_1, axiom,
% 0.18/0.46    (![A:$i]:
% 0.18/0.46     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.18/0.46       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.18/0.46  thf('8', plain, (![X7 : $i]: (v1_relat_1 @ (k6_relat_1 @ X7))),
% 0.18/0.46      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.18/0.46  thf('9', plain, (![X19 : $i]: ((k6_partfun1 @ X19) = (k6_relat_1 @ X19))),
% 0.18/0.46      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.18/0.46  thf('10', plain, (![X7 : $i]: (v1_relat_1 @ (k6_partfun1 @ X7))),
% 0.18/0.46      inference('demod', [status(thm)], ['8', '9'])).
% 0.18/0.46  thf('11', plain, (![X8 : $i]: (v1_funct_1 @ (k6_relat_1 @ X8))),
% 0.18/0.46      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.18/0.46  thf('12', plain, (![X19 : $i]: ((k6_partfun1 @ X19) = (k6_relat_1 @ X19))),
% 0.18/0.46      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.18/0.46  thf('13', plain, (![X8 : $i]: (v1_funct_1 @ (k6_partfun1 @ X8))),
% 0.18/0.46      inference('demod', [status(thm)], ['11', '12'])).
% 0.18/0.46  thf('14', plain,
% 0.18/0.46      (![X0 : $i, X1 : $i]:
% 0.18/0.46         (~ (r1_tarski @ X1 @ X0)
% 0.18/0.46          | ((k9_relat_1 @ (k6_partfun1 @ X0) @ 
% 0.18/0.46              (k10_relat_1 @ (k6_partfun1 @ X0) @ X1)) = (X1)))),
% 0.18/0.46      inference('demod', [status(thm)], ['7', '10', '13'])).
% 0.18/0.46  thf('15', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 0.18/0.46      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.18/0.46  thf('16', plain, (![X19 : $i]: ((k6_partfun1 @ X19) = (k6_relat_1 @ X19))),
% 0.18/0.46      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.18/0.46  thf('17', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X5)) = (X5))),
% 0.18/0.46      inference('demod', [status(thm)], ['15', '16'])).
% 0.18/0.46  thf(t167_relat_1, axiom,
% 0.18/0.46    (![A:$i,B:$i]:
% 0.18/0.46     ( ( v1_relat_1 @ B ) =>
% 0.18/0.46       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.18/0.46  thf('18', plain,
% 0.18/0.46      (![X3 : $i, X4 : $i]:
% 0.18/0.46         ((r1_tarski @ (k10_relat_1 @ X3 @ X4) @ (k1_relat_1 @ X3))
% 0.18/0.46          | ~ (v1_relat_1 @ X3))),
% 0.18/0.46      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.18/0.46  thf('19', plain,
% 0.18/0.46      (![X0 : $i, X1 : $i]:
% 0.18/0.46         ((r1_tarski @ (k10_relat_1 @ (k6_partfun1 @ X0) @ X1) @ X0)
% 0.18/0.46          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 0.18/0.46      inference('sup+', [status(thm)], ['17', '18'])).
% 0.18/0.46  thf('20', plain, (![X7 : $i]: (v1_relat_1 @ (k6_partfun1 @ X7))),
% 0.18/0.46      inference('demod', [status(thm)], ['8', '9'])).
% 0.18/0.46  thf('21', plain,
% 0.18/0.46      (![X0 : $i, X1 : $i]:
% 0.18/0.46         (r1_tarski @ (k10_relat_1 @ (k6_partfun1 @ X0) @ X1) @ X0)),
% 0.18/0.46      inference('demod', [status(thm)], ['19', '20'])).
% 0.18/0.46  thf('22', plain,
% 0.18/0.46      (![X0 : $i, X2 : $i]:
% 0.18/0.46         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.18/0.46      inference('cnf', [status(esa)], [t3_subset])).
% 0.18/0.46  thf('23', plain,
% 0.18/0.46      (![X0 : $i, X1 : $i]:
% 0.18/0.46         (m1_subset_1 @ (k10_relat_1 @ (k6_partfun1 @ X0) @ X1) @ 
% 0.18/0.46          (k1_zfmisc_1 @ X0))),
% 0.18/0.46      inference('sup-', [status(thm)], ['21', '22'])).
% 0.18/0.46  thf(t162_funct_1, axiom,
% 0.18/0.46    (![A:$i,B:$i]:
% 0.18/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.18/0.46       ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ))).
% 0.18/0.46  thf('24', plain,
% 0.18/0.46      (![X11 : $i, X12 : $i]:
% 0.18/0.46         (((k9_relat_1 @ (k6_relat_1 @ X12) @ X11) = (X11))
% 0.18/0.46          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.18/0.46      inference('cnf', [status(esa)], [t162_funct_1])).
% 0.18/0.46  thf('25', plain, (![X19 : $i]: ((k6_partfun1 @ X19) = (k6_relat_1 @ X19))),
% 0.18/0.46      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.18/0.46  thf('26', plain,
% 0.18/0.46      (![X11 : $i, X12 : $i]:
% 0.18/0.46         (((k9_relat_1 @ (k6_partfun1 @ X12) @ X11) = (X11))
% 0.18/0.46          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.18/0.46      inference('demod', [status(thm)], ['24', '25'])).
% 0.18/0.46  thf('27', plain,
% 0.18/0.46      (![X0 : $i, X1 : $i]:
% 0.18/0.46         ((k9_relat_1 @ (k6_partfun1 @ X0) @ 
% 0.18/0.46           (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 0.18/0.46           = (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.18/0.46      inference('sup-', [status(thm)], ['23', '26'])).
% 0.18/0.46  thf('28', plain,
% 0.18/0.46      (![X0 : $i, X1 : $i]:
% 0.18/0.46         (~ (r1_tarski @ X1 @ X0)
% 0.18/0.46          | ((k10_relat_1 @ (k6_partfun1 @ X0) @ X1) = (X1)))),
% 0.18/0.46      inference('demod', [status(thm)], ['14', '27'])).
% 0.18/0.46  thf('29', plain, (((k10_relat_1 @ (k6_partfun1 @ sk_A) @ sk_B) = (sk_B))),
% 0.18/0.46      inference('sup-', [status(thm)], ['2', '28'])).
% 0.18/0.46  thf('30', plain,
% 0.18/0.46      (((k8_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ sk_B) != (sk_B))),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf(dt_k6_partfun1, axiom,
% 0.18/0.46    (![A:$i]:
% 0.18/0.46     ( ( m1_subset_1 @
% 0.18/0.46         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.18/0.46       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.18/0.46  thf('31', plain,
% 0.18/0.46      (![X18 : $i]:
% 0.18/0.46         (m1_subset_1 @ (k6_partfun1 @ X18) @ 
% 0.18/0.46          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))),
% 0.18/0.46      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.18/0.46  thf(redefinition_k8_relset_1, axiom,
% 0.18/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.18/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.18/0.46       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.18/0.46  thf('32', plain,
% 0.18/0.46      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.18/0.46         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.18/0.46          | ((k8_relset_1 @ X14 @ X15 @ X13 @ X16) = (k10_relat_1 @ X13 @ X16)))),
% 0.18/0.46      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.18/0.46  thf('33', plain,
% 0.18/0.46      (![X0 : $i, X1 : $i]:
% 0.18/0.46         ((k8_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 0.18/0.46           = (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.18/0.46      inference('sup-', [status(thm)], ['31', '32'])).
% 0.18/0.46  thf('34', plain, (((k10_relat_1 @ (k6_partfun1 @ sk_A) @ sk_B) != (sk_B))),
% 0.18/0.46      inference('demod', [status(thm)], ['30', '33'])).
% 0.18/0.46  thf('35', plain, ($false),
% 0.18/0.46      inference('simplify_reflect-', [status(thm)], ['29', '34'])).
% 0.18/0.46  
% 0.18/0.46  % SZS output end Refutation
% 0.18/0.46  
% 0.18/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
