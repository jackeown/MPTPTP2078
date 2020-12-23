%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JBVNsg76RW

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 107 expanded)
%              Number of leaves         :   32 (  48 expanded)
%              Depth                    :   13
%              Number of atoms          :  459 ( 635 expanded)
%              Number of equality atoms :   35 (  54 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(fc24_relat_1,axiom,(
    ! [A: $i] :
      ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X20: $i] :
      ( v4_relat_1 @ ( k6_relat_1 @ X20 ) @ X20 ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X27: $i] :
      ( ( k6_partfun1 @ X27 )
      = ( k6_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('2',plain,(
    ! [X20: $i] :
      ( v4_relat_1 @ ( k6_partfun1 @ X20 ) @ X20 ) ),
    inference(demod,[status(thm)],['0','1'])).

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

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('5',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('6',plain,(
    ! [X5: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('7',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['5','6'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( r1_tarski @ X3 @ X1 )
      | ( X2
       != ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('9',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X3 @ X1 )
      | ~ ( r2_hidden @ X3 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['7','9'])).

thf(t217_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v4_relat_1 @ C @ A ) )
         => ( v4_relat_1 @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v4_relat_1 @ X12 @ X13 )
      | ( v4_relat_1 @ X12 @ X14 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t217_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ X0 @ sk_A )
      | ~ ( v4_relat_1 @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    | ( v4_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['2','12'])).

thf('14',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('15',plain,(
    ! [X27: $i] :
      ( ( k6_partfun1 @ X27 )
      = ( k6_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('16',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X19 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    v4_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['13','16'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10
        = ( k7_relat_1 @ X10 @ X11 ) )
      | ~ ( v4_relat_1 @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    | ( ( k6_partfun1 @ sk_B )
      = ( k7_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X19 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('21',plain,
    ( ( k6_partfun1 @ sk_B )
    = ( k7_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('22',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k7_relat_1 @ X18 @ X17 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X17 ) @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('23',plain,(
    ! [X27: $i] :
      ( ( k6_partfun1 @ X27 )
      = ( k6_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('24',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k7_relat_1 @ X18 @ X17 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X17 ) @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('25',plain,(
    ! [X15: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('26',plain,(
    ! [X27: $i] :
      ( ( k6_partfun1 @ X27 )
      = ( k6_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('27',plain,(
    ! [X15: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X15 ) )
      = X15 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('28',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) )
        = ( k10_relat_1 @ X9 @ ( k1_relat_1 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X19 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_partfun1 @ X1 ) @ X0 ) )
        = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','31'])).

thf('33',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X19 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('34',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X19 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_partfun1 @ X1 ) @ X0 ) )
      = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    = ( k10_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['21','35'])).

thf('37',plain,(
    ! [X15: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X15 ) )
      = X15 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('38',plain,
    ( sk_B
    = ( k10_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ( k8_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('40',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('41',plain,(
    ! [X27: $i] :
      ( ( k6_partfun1 @ X27 )
      = ( k6_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('42',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X26 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('43',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( ( k8_relset_1 @ X23 @ X24 @ X22 @ X25 )
        = ( k10_relat_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ( k10_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(demod,[status(thm)],['39','44'])).

thf('46',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['38','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JBVNsg76RW
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:04:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 39 iterations in 0.021s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.48  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.48  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.48  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.48  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.21/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.48  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.48  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(fc24_relat_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.21/0.48       ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.21/0.48       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.21/0.48  thf('0', plain, (![X20 : $i]: (v4_relat_1 @ (k6_relat_1 @ X20) @ X20)),
% 0.21/0.48      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.48  thf(redefinition_k6_partfun1, axiom,
% 0.21/0.48    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.21/0.48  thf('1', plain, (![X27 : $i]: ((k6_partfun1 @ X27) = (k6_relat_1 @ X27))),
% 0.21/0.48      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.48  thf('2', plain, (![X20 : $i]: (v4_relat_1 @ (k6_partfun1 @ X20) @ X20)),
% 0.21/0.48      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.48  thf(t171_funct_2, conjecture,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.48       ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i]:
% 0.21/0.48        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.48          ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t171_funct_2])).
% 0.21/0.48  thf('3', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t2_subset, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.48       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i]:
% 0.21/0.48         ((r2_hidden @ X6 @ X7)
% 0.21/0.48          | (v1_xboole_0 @ X7)
% 0.21/0.48          | ~ (m1_subset_1 @ X6 @ X7))),
% 0.21/0.48      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.48        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.48  thf(fc1_subset_1, axiom,
% 0.21/0.48    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.48  thf('6', plain, (![X5 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.21/0.48  thf('7', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.48      inference('clc', [status(thm)], ['5', '6'])).
% 0.21/0.48  thf(d1_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.21/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X3 @ X2)
% 0.21/0.48          | (r1_tarski @ X3 @ X1)
% 0.21/0.48          | ((X2) != (k1_zfmisc_1 @ X1)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X1 : $i, X3 : $i]:
% 0.21/0.48         ((r1_tarski @ X3 @ X1) | ~ (r2_hidden @ X3 @ (k1_zfmisc_1 @ X1)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.48  thf('10', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.21/0.48      inference('sup-', [status(thm)], ['7', '9'])).
% 0.21/0.48  thf(t217_relat_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( r1_tarski @ A @ B ) =>
% 0.21/0.48       ( ![C:$i]:
% 0.21/0.48         ( ( ( v1_relat_1 @ C ) & ( v4_relat_1 @ C @ A ) ) =>
% 0.21/0.48           ( v4_relat_1 @ C @ B ) ) ) ))).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X12)
% 0.21/0.48          | ~ (v4_relat_1 @ X12 @ X13)
% 0.21/0.48          | (v4_relat_1 @ X12 @ X14)
% 0.21/0.48          | ~ (r1_tarski @ X13 @ X14))),
% 0.21/0.48      inference('cnf', [status(esa)], [t217_relat_1])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((v4_relat_1 @ X0 @ sk_A)
% 0.21/0.48          | ~ (v4_relat_1 @ X0 @ sk_B)
% 0.21/0.48          | ~ (v1_relat_1 @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      ((~ (v1_relat_1 @ (k6_partfun1 @ sk_B))
% 0.21/0.48        | (v4_relat_1 @ (k6_partfun1 @ sk_B) @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['2', '12'])).
% 0.21/0.48  thf('14', plain, (![X19 : $i]: (v1_relat_1 @ (k6_relat_1 @ X19))),
% 0.21/0.48      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.48  thf('15', plain, (![X27 : $i]: ((k6_partfun1 @ X27) = (k6_relat_1 @ X27))),
% 0.21/0.48      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.48  thf('16', plain, (![X19 : $i]: (v1_relat_1 @ (k6_partfun1 @ X19))),
% 0.21/0.48      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.48  thf('17', plain, ((v4_relat_1 @ (k6_partfun1 @ sk_B) @ sk_A)),
% 0.21/0.48      inference('demod', [status(thm)], ['13', '16'])).
% 0.21/0.48  thf(t209_relat_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.21/0.48       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (![X10 : $i, X11 : $i]:
% 0.21/0.48         (((X10) = (k7_relat_1 @ X10 @ X11))
% 0.21/0.48          | ~ (v4_relat_1 @ X10 @ X11)
% 0.21/0.48          | ~ (v1_relat_1 @ X10))),
% 0.21/0.48      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      ((~ (v1_relat_1 @ (k6_partfun1 @ sk_B))
% 0.21/0.48        | ((k6_partfun1 @ sk_B) = (k7_relat_1 @ (k6_partfun1 @ sk_B) @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.48  thf('20', plain, (![X19 : $i]: (v1_relat_1 @ (k6_partfun1 @ X19))),
% 0.21/0.48      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (((k6_partfun1 @ sk_B) = (k7_relat_1 @ (k6_partfun1 @ sk_B) @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.48  thf(t94_relat_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ B ) =>
% 0.21/0.48       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      (![X17 : $i, X18 : $i]:
% 0.21/0.48         (((k7_relat_1 @ X18 @ X17) = (k5_relat_1 @ (k6_relat_1 @ X17) @ X18))
% 0.21/0.48          | ~ (v1_relat_1 @ X18))),
% 0.21/0.48      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.21/0.48  thf('23', plain, (![X27 : $i]: ((k6_partfun1 @ X27) = (k6_relat_1 @ X27))),
% 0.21/0.48      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      (![X17 : $i, X18 : $i]:
% 0.21/0.48         (((k7_relat_1 @ X18 @ X17) = (k5_relat_1 @ (k6_partfun1 @ X17) @ X18))
% 0.21/0.48          | ~ (v1_relat_1 @ X18))),
% 0.21/0.48      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.48  thf(t71_relat_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.21/0.48       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.48  thf('25', plain, (![X15 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X15)) = (X15))),
% 0.21/0.48      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.48  thf('26', plain, (![X27 : $i]: ((k6_partfun1 @ X27) = (k6_relat_1 @ X27))),
% 0.21/0.48      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.48  thf('27', plain, (![X15 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X15)) = (X15))),
% 0.21/0.48      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.48  thf(t182_relat_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( v1_relat_1 @ B ) =>
% 0.21/0.48           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.21/0.48             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      (![X8 : $i, X9 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X8)
% 0.21/0.48          | ((k1_relat_1 @ (k5_relat_1 @ X9 @ X8))
% 0.21/0.48              = (k10_relat_1 @ X9 @ (k1_relat_1 @ X8)))
% 0.21/0.48          | ~ (v1_relat_1 @ X9))),
% 0.21/0.48      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0)))
% 0.21/0.48            = (k10_relat_1 @ X1 @ X0))
% 0.21/0.48          | ~ (v1_relat_1 @ X1)
% 0.21/0.48          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 0.21/0.48      inference('sup+', [status(thm)], ['27', '28'])).
% 0.21/0.48  thf('30', plain, (![X19 : $i]: (v1_relat_1 @ (k6_partfun1 @ X19))),
% 0.21/0.48      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.48  thf('31', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0)))
% 0.21/0.48            = (k10_relat_1 @ X1 @ X0))
% 0.21/0.48          | ~ (v1_relat_1 @ X1))),
% 0.21/0.48      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.48  thf('32', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (((k1_relat_1 @ (k7_relat_1 @ (k6_partfun1 @ X1) @ X0))
% 0.21/0.48            = (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 0.21/0.48          | ~ (v1_relat_1 @ (k6_partfun1 @ X1))
% 0.21/0.48          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 0.21/0.48      inference('sup+', [status(thm)], ['24', '31'])).
% 0.21/0.48  thf('33', plain, (![X19 : $i]: (v1_relat_1 @ (k6_partfun1 @ X19))),
% 0.21/0.48      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.48  thf('34', plain, (![X19 : $i]: (v1_relat_1 @ (k6_partfun1 @ X19))),
% 0.21/0.48      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.48  thf('35', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((k1_relat_1 @ (k7_relat_1 @ (k6_partfun1 @ X1) @ X0))
% 0.21/0.48           = (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.21/0.48      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.21/0.48  thf('36', plain,
% 0.21/0.48      (((k1_relat_1 @ (k6_partfun1 @ sk_B))
% 0.21/0.48         = (k10_relat_1 @ (k6_partfun1 @ sk_A) @ sk_B))),
% 0.21/0.48      inference('sup+', [status(thm)], ['21', '35'])).
% 0.21/0.48  thf('37', plain, (![X15 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X15)) = (X15))),
% 0.21/0.48      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.48  thf('38', plain, (((sk_B) = (k10_relat_1 @ (k6_partfun1 @ sk_A) @ sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['36', '37'])).
% 0.21/0.48  thf('39', plain,
% 0.21/0.48      (((k8_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ sk_B) != (sk_B))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t29_relset_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( m1_subset_1 @
% 0.21/0.48       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.21/0.48  thf('40', plain,
% 0.21/0.48      (![X26 : $i]:
% 0.21/0.48         (m1_subset_1 @ (k6_relat_1 @ X26) @ 
% 0.21/0.48          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X26)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.21/0.48  thf('41', plain, (![X27 : $i]: ((k6_partfun1 @ X27) = (k6_relat_1 @ X27))),
% 0.21/0.48      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.48  thf('42', plain,
% 0.21/0.48      (![X26 : $i]:
% 0.21/0.48         (m1_subset_1 @ (k6_partfun1 @ X26) @ 
% 0.21/0.48          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X26)))),
% 0.21/0.48      inference('demod', [status(thm)], ['40', '41'])).
% 0.21/0.48  thf(redefinition_k8_relset_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.48       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.21/0.48  thf('43', plain,
% 0.21/0.48      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.21/0.48          | ((k8_relset_1 @ X23 @ X24 @ X22 @ X25) = (k10_relat_1 @ X22 @ X25)))),
% 0.21/0.48      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.21/0.48  thf('44', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((k8_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 0.21/0.48           = (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.48  thf('45', plain, (((k10_relat_1 @ (k6_partfun1 @ sk_A) @ sk_B) != (sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['39', '44'])).
% 0.21/0.48  thf('46', plain, ($false),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['38', '45'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
