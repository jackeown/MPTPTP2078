%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZjJCYMtDlJ

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:02 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   67 (  76 expanded)
%              Number of leaves         :   30 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :  381 ( 477 expanded)
%              Number of equality atoms :   28 (  32 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(fc24_relat_1,axiom,(
    ! [A: $i] :
      ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X15: $i] :
      ( v4_relat_1 @ ( k6_relat_1 @ X15 ) @ X15 ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf(t162_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t162_funct_1])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('3',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t217_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v4_relat_1 @ C @ A ) )
         => ( v4_relat_1 @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v4_relat_1 @ X7 @ X8 )
      | ( v4_relat_1 @ X7 @ X9 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t217_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ X0 @ sk_A )
      | ~ ( v4_relat_1 @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
    | ( v4_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('8',plain,(
    v4_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['6','7'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X5
        = ( k7_relat_1 @ X5 @ X6 ) )
      | ~ ( v4_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
    | ( ( k6_relat_1 @ sk_B )
      = ( k7_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('12',plain,
    ( ( k6_relat_1 @ sk_B )
    = ( k7_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k7_relat_1 @ X13 @ X12 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X12 ) @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('14',plain,(
    ! [X10: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X4 @ X3 ) )
        = ( k10_relat_1 @ X4 @ ( k1_relat_1 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('21',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ( k1_relat_1 @ ( k6_relat_1 @ sk_B ) )
    = ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['12','22'])).

thf('24',plain,(
    ! [X10: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('25',plain,
    ( sk_B
    = ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ( k9_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_1,axiom,(
    ! [A: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('27',plain,(
    ! [X23: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ X23 ) )
      = ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_1])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('28',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k10_relat_1 @ X21 @ X22 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X21 ) @ X22 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('31',plain,(
    ! [X18: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('32',plain,(
    ! [X20: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('34',plain,(
    ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(demod,[status(thm)],['26','33'])).

thf('35',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['25','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZjJCYMtDlJ
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:29:56 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 28 iterations in 0.015s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.49  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.22/0.49  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.49  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.49  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.22/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.49  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.22/0.49  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.49  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.49  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.49  thf(fc24_relat_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.22/0.49       ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.22/0.49       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.22/0.49  thf('0', plain, (![X15 : $i]: (v4_relat_1 @ (k6_relat_1 @ X15) @ X15)),
% 0.22/0.49      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.22/0.49  thf(t162_funct_1, conjecture,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.49       ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i,B:$i]:
% 0.22/0.49        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.49          ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t162_funct_1])).
% 0.22/0.49  thf('1', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(t3_subset, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.49  thf('3', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.22/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.49  thf(t217_relat_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( r1_tarski @ A @ B ) =>
% 0.22/0.49       ( ![C:$i]:
% 0.22/0.49         ( ( ( v1_relat_1 @ C ) & ( v4_relat_1 @ C @ A ) ) =>
% 0.22/0.49           ( v4_relat_1 @ C @ B ) ) ) ))).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.49         (~ (v1_relat_1 @ X7)
% 0.22/0.49          | ~ (v4_relat_1 @ X7 @ X8)
% 0.22/0.49          | (v4_relat_1 @ X7 @ X9)
% 0.22/0.49          | ~ (r1_tarski @ X8 @ X9))),
% 0.22/0.49      inference('cnf', [status(esa)], [t217_relat_1])).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((v4_relat_1 @ X0 @ sk_A)
% 0.22/0.49          | ~ (v4_relat_1 @ X0 @ sk_B)
% 0.22/0.49          | ~ (v1_relat_1 @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      ((~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.22/0.49        | (v4_relat_1 @ (k6_relat_1 @ sk_B) @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['0', '5'])).
% 0.22/0.49  thf('7', plain, (![X14 : $i]: (v1_relat_1 @ (k6_relat_1 @ X14))),
% 0.22/0.49      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.22/0.49  thf('8', plain, ((v4_relat_1 @ (k6_relat_1 @ sk_B) @ sk_A)),
% 0.22/0.49      inference('demod', [status(thm)], ['6', '7'])).
% 0.22/0.49  thf(t209_relat_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.22/0.49       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      (![X5 : $i, X6 : $i]:
% 0.22/0.49         (((X5) = (k7_relat_1 @ X5 @ X6))
% 0.22/0.49          | ~ (v4_relat_1 @ X5 @ X6)
% 0.22/0.49          | ~ (v1_relat_1 @ X5))),
% 0.22/0.49      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      ((~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.22/0.49        | ((k6_relat_1 @ sk_B) = (k7_relat_1 @ (k6_relat_1 @ sk_B) @ sk_A)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.49  thf('11', plain, (![X14 : $i]: (v1_relat_1 @ (k6_relat_1 @ X14))),
% 0.22/0.49      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (((k6_relat_1 @ sk_B) = (k7_relat_1 @ (k6_relat_1 @ sk_B) @ sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['10', '11'])).
% 0.22/0.49  thf(t94_relat_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( v1_relat_1 @ B ) =>
% 0.22/0.49       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      (![X12 : $i, X13 : $i]:
% 0.22/0.49         (((k7_relat_1 @ X13 @ X12) = (k5_relat_1 @ (k6_relat_1 @ X12) @ X13))
% 0.22/0.49          | ~ (v1_relat_1 @ X13))),
% 0.22/0.49      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.22/0.49  thf(t71_relat_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.22/0.49       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.22/0.49  thf('14', plain, (![X10 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 0.22/0.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.49  thf(t182_relat_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( v1_relat_1 @ A ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( v1_relat_1 @ B ) =>
% 0.22/0.49           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.22/0.49             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      (![X3 : $i, X4 : $i]:
% 0.22/0.49         (~ (v1_relat_1 @ X3)
% 0.22/0.49          | ((k1_relat_1 @ (k5_relat_1 @ X4 @ X3))
% 0.22/0.49              = (k10_relat_1 @ X4 @ (k1_relat_1 @ X3)))
% 0.22/0.49          | ~ (v1_relat_1 @ X4))),
% 0.22/0.49      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.22/0.49            = (k10_relat_1 @ X1 @ X0))
% 0.22/0.49          | ~ (v1_relat_1 @ X1)
% 0.22/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.22/0.49      inference('sup+', [status(thm)], ['14', '15'])).
% 0.22/0.49  thf('17', plain, (![X14 : $i]: (v1_relat_1 @ (k6_relat_1 @ X14))),
% 0.22/0.49      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.22/0.49            = (k10_relat_1 @ X1 @ X0))
% 0.22/0.49          | ~ (v1_relat_1 @ X1))),
% 0.22/0.49      inference('demod', [status(thm)], ['16', '17'])).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.22/0.49            = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.22/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.22/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.22/0.49      inference('sup+', [status(thm)], ['13', '18'])).
% 0.22/0.49  thf('20', plain, (![X14 : $i]: (v1_relat_1 @ (k6_relat_1 @ X14))),
% 0.22/0.49      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.22/0.49  thf('21', plain, (![X14 : $i]: (v1_relat_1 @ (k6_relat_1 @ X14))),
% 0.22/0.49      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.22/0.49  thf('22', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.22/0.49           = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.22/0.49      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.22/0.49  thf('23', plain,
% 0.22/0.49      (((k1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.22/0.49         = (k10_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 0.22/0.49      inference('sup+', [status(thm)], ['12', '22'])).
% 0.22/0.49  thf('24', plain, (![X10 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 0.22/0.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.49  thf('25', plain, (((sk_B) = (k10_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 0.22/0.49      inference('demod', [status(thm)], ['23', '24'])).
% 0.22/0.49  thf('26', plain, (((k9_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) != (sk_B))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(t67_funct_1, axiom,
% 0.22/0.49    (![A:$i]: ( ( k2_funct_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.22/0.49  thf('27', plain,
% 0.22/0.49      (![X23 : $i]: ((k2_funct_1 @ (k6_relat_1 @ X23)) = (k6_relat_1 @ X23))),
% 0.22/0.49      inference('cnf', [status(esa)], [t67_funct_1])).
% 0.22/0.49  thf(t155_funct_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.49       ( ( v2_funct_1 @ B ) =>
% 0.22/0.49         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.22/0.49  thf('28', plain,
% 0.22/0.49      (![X21 : $i, X22 : $i]:
% 0.22/0.49         (~ (v2_funct_1 @ X21)
% 0.22/0.49          | ((k10_relat_1 @ X21 @ X22)
% 0.22/0.49              = (k9_relat_1 @ (k2_funct_1 @ X21) @ X22))
% 0.22/0.49          | ~ (v1_funct_1 @ X21)
% 0.22/0.49          | ~ (v1_relat_1 @ X21))),
% 0.22/0.49      inference('cnf', [status(esa)], [t155_funct_1])).
% 0.22/0.49  thf('29', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (((k10_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.22/0.49            = (k9_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.22/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.22/0.49          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.22/0.49          | ~ (v2_funct_1 @ (k6_relat_1 @ X0)))),
% 0.22/0.49      inference('sup+', [status(thm)], ['27', '28'])).
% 0.22/0.49  thf('30', plain, (![X14 : $i]: (v1_relat_1 @ (k6_relat_1 @ X14))),
% 0.22/0.49      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.22/0.49  thf(fc3_funct_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.22/0.49       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.22/0.49  thf('31', plain, (![X18 : $i]: (v1_funct_1 @ (k6_relat_1 @ X18))),
% 0.22/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.22/0.49  thf(fc4_funct_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.22/0.49       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.22/0.49  thf('32', plain, (![X20 : $i]: (v2_funct_1 @ (k6_relat_1 @ X20))),
% 0.22/0.49      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.22/0.49  thf('33', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((k10_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.22/0.49           = (k9_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.22/0.49      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.22/0.49  thf('34', plain, (((k10_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) != (sk_B))),
% 0.22/0.49      inference('demod', [status(thm)], ['26', '33'])).
% 0.22/0.49  thf('35', plain, ($false),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['25', '34'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
