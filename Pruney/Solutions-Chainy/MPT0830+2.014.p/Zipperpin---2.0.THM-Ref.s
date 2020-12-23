%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Z2BcxQhIWZ

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:15 EST 2020

% Result     : Theorem 1.05s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 103 expanded)
%              Number of leaves         :   26 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :  467 ( 894 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_relset_1_type,type,(
    k5_relset_1: $i > $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t33_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( m1_subset_1 @ ( k5_relset_1 @ A @ C @ D @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
       => ( m1_subset_1 @ ( k5_relset_1 @ A @ C @ D @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_relset_1])).

thf('0',plain,(
    ~ ( m1_subset_1 @ ( k5_relset_1 @ sk_A @ sk_C @ sk_D @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k5_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k5_relset_1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( ( k5_relset_1 @ X19 @ X20 @ X18 @ X21 )
        = ( k7_relat_1 @ X18 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k5_relset_1 @ sk_A @ sk_C @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v4_relat_1 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('7',plain,(
    v4_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc23_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v4_relat_1 @ C @ B ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ C @ A ) )
        & ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ A )
        & ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v4_relat_1 @ ( k7_relat_1 @ X2 @ X3 ) @ X3 )
      | ~ ( v4_relat_1 @ X2 @ X4 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc23_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( v4_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('12',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['9','12'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v4_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf('17',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X3 ) )
      | ~ ( v4_relat_1 @ X2 @ X4 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc23_relat_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('20',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['15','20'])).

thf('22',plain,(
    v4_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8
        = ( k7_relat_1 @ X8 @ X9 ) )
      | ~ ( v4_relat_1 @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('26',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('27',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) @ X7 )
        = ( k7_relat_1 @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('28',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X10 @ X11 ) @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_D )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['26','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_D ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
     => ( ( r1_tarski @ A @ D )
       => ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('35',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( r1_tarski @ X26 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t4_relset_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_D )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('38',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X22 ) @ X23 )
      | ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['21','39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['4','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Z2BcxQhIWZ
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:14:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.05/1.24  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.05/1.24  % Solved by: fo/fo7.sh
% 1.05/1.24  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.05/1.24  % done 1051 iterations in 0.801s
% 1.05/1.24  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.05/1.24  % SZS output start Refutation
% 1.05/1.24  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.05/1.24  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.05/1.24  thf(sk_A_type, type, sk_A: $i).
% 1.05/1.24  thf(sk_D_type, type, sk_D: $i).
% 1.05/1.24  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.05/1.24  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.05/1.24  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.05/1.24  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.05/1.24  thf(sk_C_type, type, sk_C: $i).
% 1.05/1.24  thf(sk_B_type, type, sk_B: $i).
% 1.05/1.24  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.05/1.24  thf(k5_relset_1_type, type, k5_relset_1: $i > $i > $i > $i > $i).
% 1.05/1.24  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.05/1.24  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.05/1.24  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.05/1.24  thf(t33_relset_1, conjecture,
% 1.05/1.24    (![A:$i,B:$i,C:$i,D:$i]:
% 1.05/1.24     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 1.05/1.24       ( m1_subset_1 @
% 1.05/1.24         ( k5_relset_1 @ A @ C @ D @ B ) @ 
% 1.05/1.24         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 1.05/1.24  thf(zf_stmt_0, negated_conjecture,
% 1.05/1.24    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.05/1.24        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 1.05/1.24          ( m1_subset_1 @
% 1.05/1.24            ( k5_relset_1 @ A @ C @ D @ B ) @ 
% 1.05/1.24            ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )),
% 1.05/1.24    inference('cnf.neg', [status(esa)], [t33_relset_1])).
% 1.05/1.24  thf('0', plain,
% 1.05/1.24      (~ (m1_subset_1 @ (k5_relset_1 @ sk_A @ sk_C @ sk_D @ sk_B) @ 
% 1.05/1.24          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('1', plain,
% 1.05/1.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf(redefinition_k5_relset_1, axiom,
% 1.05/1.24    (![A:$i,B:$i,C:$i,D:$i]:
% 1.05/1.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.05/1.24       ( ( k5_relset_1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 1.05/1.24  thf('2', plain,
% 1.05/1.24      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.05/1.24         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 1.05/1.24          | ((k5_relset_1 @ X19 @ X20 @ X18 @ X21) = (k7_relat_1 @ X18 @ X21)))),
% 1.05/1.24      inference('cnf', [status(esa)], [redefinition_k5_relset_1])).
% 1.05/1.24  thf('3', plain,
% 1.05/1.24      (![X0 : $i]:
% 1.05/1.24         ((k5_relset_1 @ sk_A @ sk_C @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 1.05/1.24      inference('sup-', [status(thm)], ['1', '2'])).
% 1.05/1.24  thf('4', plain,
% 1.05/1.24      (~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_B) @ 
% 1.05/1.24          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.05/1.24      inference('demod', [status(thm)], ['0', '3'])).
% 1.05/1.24  thf('5', plain,
% 1.05/1.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf(cc2_relset_1, axiom,
% 1.05/1.24    (![A:$i,B:$i,C:$i]:
% 1.05/1.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.05/1.24       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.05/1.24  thf('6', plain,
% 1.05/1.24      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.05/1.24         ((v4_relat_1 @ X15 @ X16)
% 1.05/1.24          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 1.05/1.24      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.05/1.24  thf('7', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 1.05/1.24      inference('sup-', [status(thm)], ['5', '6'])).
% 1.05/1.24  thf(fc23_relat_1, axiom,
% 1.05/1.24    (![A:$i,B:$i,C:$i]:
% 1.05/1.24     ( ( ( v1_relat_1 @ C ) & ( v4_relat_1 @ C @ B ) ) =>
% 1.05/1.24       ( ( v1_relat_1 @ ( k7_relat_1 @ C @ A ) ) & 
% 1.05/1.24         ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ A ) & 
% 1.05/1.24         ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) ) ))).
% 1.05/1.24  thf('8', plain,
% 1.05/1.24      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.05/1.24         ((v4_relat_1 @ (k7_relat_1 @ X2 @ X3) @ X3)
% 1.05/1.24          | ~ (v4_relat_1 @ X2 @ X4)
% 1.05/1.24          | ~ (v1_relat_1 @ X2))),
% 1.05/1.24      inference('cnf', [status(esa)], [fc23_relat_1])).
% 1.05/1.24  thf('9', plain,
% 1.05/1.24      (![X0 : $i]:
% 1.05/1.24         (~ (v1_relat_1 @ sk_D) | (v4_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ X0))),
% 1.05/1.24      inference('sup-', [status(thm)], ['7', '8'])).
% 1.05/1.24  thf('10', plain,
% 1.05/1.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf(cc1_relset_1, axiom,
% 1.05/1.24    (![A:$i,B:$i,C:$i]:
% 1.05/1.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.05/1.24       ( v1_relat_1 @ C ) ))).
% 1.05/1.24  thf('11', plain,
% 1.05/1.24      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.05/1.24         ((v1_relat_1 @ X12)
% 1.05/1.24          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.05/1.24      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.05/1.24  thf('12', plain, ((v1_relat_1 @ sk_D)),
% 1.05/1.24      inference('sup-', [status(thm)], ['10', '11'])).
% 1.05/1.24  thf('13', plain, (![X0 : $i]: (v4_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ X0)),
% 1.05/1.24      inference('demod', [status(thm)], ['9', '12'])).
% 1.05/1.24  thf(d18_relat_1, axiom,
% 1.05/1.24    (![A:$i,B:$i]:
% 1.05/1.24     ( ( v1_relat_1 @ B ) =>
% 1.05/1.24       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.05/1.24  thf('14', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i]:
% 1.05/1.24         (~ (v4_relat_1 @ X0 @ X1)
% 1.05/1.24          | (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 1.05/1.24          | ~ (v1_relat_1 @ X0))),
% 1.05/1.24      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.05/1.24  thf('15', plain,
% 1.05/1.24      (![X0 : $i]:
% 1.05/1.24         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 1.05/1.24          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X0))),
% 1.05/1.24      inference('sup-', [status(thm)], ['13', '14'])).
% 1.05/1.24  thf('16', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 1.05/1.24      inference('sup-', [status(thm)], ['5', '6'])).
% 1.05/1.24  thf('17', plain,
% 1.05/1.24      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.05/1.24         ((v1_relat_1 @ (k7_relat_1 @ X2 @ X3))
% 1.05/1.24          | ~ (v4_relat_1 @ X2 @ X4)
% 1.05/1.24          | ~ (v1_relat_1 @ X2))),
% 1.05/1.24      inference('cnf', [status(esa)], [fc23_relat_1])).
% 1.05/1.24  thf('18', plain,
% 1.05/1.24      (![X0 : $i]:
% 1.05/1.24         (~ (v1_relat_1 @ sk_D) | (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 1.05/1.24      inference('sup-', [status(thm)], ['16', '17'])).
% 1.05/1.24  thf('19', plain, ((v1_relat_1 @ sk_D)),
% 1.05/1.24      inference('sup-', [status(thm)], ['10', '11'])).
% 1.05/1.24  thf('20', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 1.05/1.24      inference('demod', [status(thm)], ['18', '19'])).
% 1.05/1.24  thf('21', plain,
% 1.05/1.24      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X0)),
% 1.05/1.24      inference('demod', [status(thm)], ['15', '20'])).
% 1.05/1.24  thf('22', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 1.05/1.24      inference('sup-', [status(thm)], ['5', '6'])).
% 1.05/1.24  thf(t209_relat_1, axiom,
% 1.05/1.24    (![A:$i,B:$i]:
% 1.05/1.24     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.05/1.24       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 1.05/1.24  thf('23', plain,
% 1.05/1.24      (![X8 : $i, X9 : $i]:
% 1.05/1.24         (((X8) = (k7_relat_1 @ X8 @ X9))
% 1.05/1.24          | ~ (v4_relat_1 @ X8 @ X9)
% 1.05/1.24          | ~ (v1_relat_1 @ X8))),
% 1.05/1.24      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.05/1.24  thf('24', plain,
% 1.05/1.24      ((~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ sk_A)))),
% 1.05/1.24      inference('sup-', [status(thm)], ['22', '23'])).
% 1.05/1.24  thf('25', plain, ((v1_relat_1 @ sk_D)),
% 1.05/1.24      inference('sup-', [status(thm)], ['10', '11'])).
% 1.05/1.24  thf('26', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_A))),
% 1.05/1.24      inference('demod', [status(thm)], ['24', '25'])).
% 1.05/1.24  thf(t100_relat_1, axiom,
% 1.05/1.24    (![A:$i,B:$i,C:$i]:
% 1.05/1.24     ( ( v1_relat_1 @ C ) =>
% 1.05/1.24       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 1.05/1.24         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 1.05/1.24  thf('27', plain,
% 1.05/1.24      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.05/1.24         (((k7_relat_1 @ (k7_relat_1 @ X5 @ X6) @ X7)
% 1.05/1.24            = (k7_relat_1 @ X5 @ (k3_xboole_0 @ X6 @ X7)))
% 1.05/1.24          | ~ (v1_relat_1 @ X5))),
% 1.05/1.24      inference('cnf', [status(esa)], [t100_relat_1])).
% 1.05/1.24  thf(t88_relat_1, axiom,
% 1.05/1.24    (![A:$i,B:$i]:
% 1.05/1.24     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 1.05/1.24  thf('28', plain,
% 1.05/1.24      (![X10 : $i, X11 : $i]:
% 1.05/1.24         ((r1_tarski @ (k7_relat_1 @ X10 @ X11) @ X10) | ~ (v1_relat_1 @ X10))),
% 1.05/1.24      inference('cnf', [status(esa)], [t88_relat_1])).
% 1.05/1.24  thf('29', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.24         ((r1_tarski @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0) @ X2)
% 1.05/1.24          | ~ (v1_relat_1 @ X2)
% 1.05/1.24          | ~ (v1_relat_1 @ X2))),
% 1.05/1.24      inference('sup+', [status(thm)], ['27', '28'])).
% 1.05/1.24  thf('30', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.24         (~ (v1_relat_1 @ X2)
% 1.05/1.24          | (r1_tarski @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0) @ X2))),
% 1.05/1.24      inference('simplify', [status(thm)], ['29'])).
% 1.05/1.24  thf('31', plain,
% 1.05/1.24      (![X0 : $i]:
% 1.05/1.24         ((r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ sk_D) | ~ (v1_relat_1 @ sk_D))),
% 1.05/1.24      inference('sup+', [status(thm)], ['26', '30'])).
% 1.05/1.24  thf('32', plain, ((v1_relat_1 @ sk_D)),
% 1.05/1.24      inference('sup-', [status(thm)], ['10', '11'])).
% 1.05/1.24  thf('33', plain, (![X0 : $i]: (r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ sk_D)),
% 1.05/1.24      inference('demod', [status(thm)], ['31', '32'])).
% 1.05/1.24  thf('34', plain,
% 1.05/1.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf(t4_relset_1, axiom,
% 1.05/1.24    (![A:$i,B:$i,C:$i,D:$i]:
% 1.05/1.24     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 1.05/1.24       ( ( r1_tarski @ A @ D ) =>
% 1.05/1.24         ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 1.05/1.24  thf('35', plain,
% 1.05/1.24      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.05/1.24         ((m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 1.05/1.24          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 1.05/1.24          | ~ (r1_tarski @ X26 @ X29))),
% 1.05/1.24      inference('cnf', [status(esa)], [t4_relset_1])).
% 1.05/1.24  thf('36', plain,
% 1.05/1.24      (![X0 : $i]:
% 1.05/1.24         (~ (r1_tarski @ X0 @ sk_D)
% 1.05/1.24          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 1.05/1.24      inference('sup-', [status(thm)], ['34', '35'])).
% 1.05/1.24  thf('37', plain,
% 1.05/1.24      (![X0 : $i]:
% 1.05/1.24         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 1.05/1.24          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.05/1.24      inference('sup-', [status(thm)], ['33', '36'])).
% 1.05/1.24  thf(t13_relset_1, axiom,
% 1.05/1.24    (![A:$i,B:$i,C:$i,D:$i]:
% 1.05/1.24     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 1.05/1.24       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 1.05/1.24         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 1.05/1.24  thf('38', plain,
% 1.05/1.24      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 1.05/1.24         (~ (r1_tarski @ (k1_relat_1 @ X22) @ X23)
% 1.05/1.24          | (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 1.05/1.24          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 1.05/1.24      inference('cnf', [status(esa)], [t13_relset_1])).
% 1.05/1.24  thf('39', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i]:
% 1.05/1.24         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 1.05/1.24           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C)))
% 1.05/1.24          | ~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X1))),
% 1.05/1.24      inference('sup-', [status(thm)], ['37', '38'])).
% 1.05/1.24  thf('40', plain,
% 1.05/1.24      (![X0 : $i]:
% 1.05/1.24         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 1.05/1.24          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_C)))),
% 1.05/1.24      inference('sup-', [status(thm)], ['21', '39'])).
% 1.05/1.24  thf('41', plain, ($false), inference('demod', [status(thm)], ['4', '40'])).
% 1.05/1.24  
% 1.05/1.24  % SZS output end Refutation
% 1.05/1.24  
% 1.05/1.25  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
