%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LQ6NHRPnGk

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:15 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   60 (  96 expanded)
%              Number of leaves         :   24 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :  399 ( 781 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k5_relset_1_type,type,(
    k5_relset_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ~ ( m1_subset_1 @ ( k5_relset_1 @ sk_A @ sk_C_1 @ sk_D @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k5_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k5_relset_1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k5_relset_1 @ X28 @ X29 @ X27 @ X30 )
        = ( k7_relat_1 @ X27 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k5_relset_1 @ sk_A @ sk_C_1 @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v4_relat_1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v4_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) @ X17 )
      | ~ ( v4_relat_1 @ X16 @ X18 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc23_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( v4_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('11',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ~ ( v4_relat_1 @ X14 @ X15 )
      | ( r1_tarski @ ( k1_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('19',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X19 @ X20 ) @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['15','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('31',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X31 ) @ X32 )
      | ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C_1 ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['4','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LQ6NHRPnGk
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:20:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.48/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.48/0.64  % Solved by: fo/fo7.sh
% 0.48/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.64  % done 271 iterations in 0.184s
% 0.48/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.48/0.64  % SZS output start Refutation
% 0.48/0.64  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.48/0.64  thf(sk_D_type, type, sk_D: $i).
% 0.48/0.64  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.48/0.64  thf(k5_relset_1_type, type, k5_relset_1: $i > $i > $i > $i > $i).
% 0.48/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.48/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.48/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.48/0.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.48/0.64  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.48/0.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.48/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.64  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.48/0.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.48/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.48/0.64  thf(t33_relset_1, conjecture,
% 0.48/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.64     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.48/0.64       ( m1_subset_1 @
% 0.48/0.64         ( k5_relset_1 @ A @ C @ D @ B ) @ 
% 0.48/0.64         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.48/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.64    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.64        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.48/0.64          ( m1_subset_1 @
% 0.48/0.64            ( k5_relset_1 @ A @ C @ D @ B ) @ 
% 0.48/0.64            ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )),
% 0.48/0.64    inference('cnf.neg', [status(esa)], [t33_relset_1])).
% 0.48/0.64  thf('0', plain,
% 0.48/0.64      (~ (m1_subset_1 @ (k5_relset_1 @ sk_A @ sk_C_1 @ sk_D @ sk_B) @ 
% 0.48/0.64          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.48/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.64  thf('1', plain,
% 0.48/0.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.48/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.64  thf(redefinition_k5_relset_1, axiom,
% 0.48/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.64       ( ( k5_relset_1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.48/0.64  thf('2', plain,
% 0.48/0.64      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.48/0.64         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.48/0.64          | ((k5_relset_1 @ X28 @ X29 @ X27 @ X30) = (k7_relat_1 @ X27 @ X30)))),
% 0.48/0.64      inference('cnf', [status(esa)], [redefinition_k5_relset_1])).
% 0.48/0.64  thf('3', plain,
% 0.48/0.64      (![X0 : $i]:
% 0.48/0.64         ((k5_relset_1 @ sk_A @ sk_C_1 @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.48/0.64      inference('sup-', [status(thm)], ['1', '2'])).
% 0.48/0.64  thf('4', plain,
% 0.48/0.64      (~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_B) @ 
% 0.48/0.64          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.48/0.64      inference('demod', [status(thm)], ['0', '3'])).
% 0.48/0.64  thf('5', plain,
% 0.48/0.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.48/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.64  thf(cc2_relset_1, axiom,
% 0.48/0.64    (![A:$i,B:$i,C:$i]:
% 0.48/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.64       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.48/0.64  thf('6', plain,
% 0.48/0.64      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.48/0.64         ((v4_relat_1 @ X24 @ X25)
% 0.48/0.64          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.48/0.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.48/0.64  thf('7', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 0.48/0.64      inference('sup-', [status(thm)], ['5', '6'])).
% 0.48/0.64  thf(fc23_relat_1, axiom,
% 0.48/0.64    (![A:$i,B:$i,C:$i]:
% 0.48/0.64     ( ( ( v1_relat_1 @ C ) & ( v4_relat_1 @ C @ B ) ) =>
% 0.48/0.64       ( ( v1_relat_1 @ ( k7_relat_1 @ C @ A ) ) & 
% 0.48/0.64         ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ A ) & 
% 0.48/0.64         ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) ) ))).
% 0.48/0.64  thf('8', plain,
% 0.48/0.64      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.48/0.64         ((v4_relat_1 @ (k7_relat_1 @ X16 @ X17) @ X17)
% 0.48/0.64          | ~ (v4_relat_1 @ X16 @ X18)
% 0.48/0.64          | ~ (v1_relat_1 @ X16))),
% 0.48/0.64      inference('cnf', [status(esa)], [fc23_relat_1])).
% 0.48/0.64  thf('9', plain,
% 0.48/0.64      (![X0 : $i]:
% 0.48/0.64         (~ (v1_relat_1 @ sk_D) | (v4_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ X0))),
% 0.48/0.64      inference('sup-', [status(thm)], ['7', '8'])).
% 0.48/0.64  thf('10', plain,
% 0.48/0.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.48/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.64  thf(cc1_relset_1, axiom,
% 0.48/0.64    (![A:$i,B:$i,C:$i]:
% 0.48/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.64       ( v1_relat_1 @ C ) ))).
% 0.48/0.64  thf('11', plain,
% 0.48/0.64      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.48/0.64         ((v1_relat_1 @ X21)
% 0.48/0.64          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.48/0.64      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.48/0.64  thf('12', plain, ((v1_relat_1 @ sk_D)),
% 0.48/0.64      inference('sup-', [status(thm)], ['10', '11'])).
% 0.48/0.64  thf('13', plain, (![X0 : $i]: (v4_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ X0)),
% 0.48/0.64      inference('demod', [status(thm)], ['9', '12'])).
% 0.48/0.64  thf(d18_relat_1, axiom,
% 0.48/0.64    (![A:$i,B:$i]:
% 0.48/0.64     ( ( v1_relat_1 @ B ) =>
% 0.48/0.64       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.48/0.64  thf('14', plain,
% 0.48/0.64      (![X14 : $i, X15 : $i]:
% 0.48/0.64         (~ (v4_relat_1 @ X14 @ X15)
% 0.48/0.64          | (r1_tarski @ (k1_relat_1 @ X14) @ X15)
% 0.48/0.64          | ~ (v1_relat_1 @ X14))),
% 0.48/0.64      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.48/0.64  thf('15', plain,
% 0.48/0.64      (![X0 : $i]:
% 0.48/0.64         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 0.48/0.64          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X0))),
% 0.48/0.64      inference('sup-', [status(thm)], ['13', '14'])).
% 0.48/0.64  thf('16', plain,
% 0.48/0.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.48/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.64  thf(t3_subset, axiom,
% 0.48/0.64    (![A:$i,B:$i]:
% 0.48/0.64     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.48/0.64  thf('17', plain,
% 0.48/0.64      (![X11 : $i, X12 : $i]:
% 0.48/0.64         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.48/0.64      inference('cnf', [status(esa)], [t3_subset])).
% 0.48/0.64  thf('18', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_C_1))),
% 0.48/0.64      inference('sup-', [status(thm)], ['16', '17'])).
% 0.48/0.64  thf(t88_relat_1, axiom,
% 0.48/0.64    (![A:$i,B:$i]:
% 0.48/0.64     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 0.48/0.64  thf('19', plain,
% 0.48/0.64      (![X19 : $i, X20 : $i]:
% 0.48/0.64         ((r1_tarski @ (k7_relat_1 @ X19 @ X20) @ X19) | ~ (v1_relat_1 @ X19))),
% 0.48/0.64      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.48/0.64  thf(t1_xboole_1, axiom,
% 0.48/0.64    (![A:$i,B:$i,C:$i]:
% 0.48/0.64     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.48/0.64       ( r1_tarski @ A @ C ) ))).
% 0.48/0.64  thf('20', plain,
% 0.48/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.64         (~ (r1_tarski @ X0 @ X1)
% 0.48/0.64          | ~ (r1_tarski @ X1 @ X2)
% 0.48/0.64          | (r1_tarski @ X0 @ X2))),
% 0.48/0.64      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.48/0.64  thf('21', plain,
% 0.48/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.64         (~ (v1_relat_1 @ X0)
% 0.48/0.64          | (r1_tarski @ (k7_relat_1 @ X0 @ X1) @ X2)
% 0.48/0.64          | ~ (r1_tarski @ X0 @ X2))),
% 0.48/0.64      inference('sup-', [status(thm)], ['19', '20'])).
% 0.48/0.64  thf('22', plain,
% 0.48/0.64      (![X0 : $i]:
% 0.48/0.64         ((r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_C_1))
% 0.48/0.64          | ~ (v1_relat_1 @ sk_D))),
% 0.48/0.64      inference('sup-', [status(thm)], ['18', '21'])).
% 0.48/0.64  thf('23', plain, ((v1_relat_1 @ sk_D)),
% 0.48/0.64      inference('sup-', [status(thm)], ['10', '11'])).
% 0.48/0.64  thf('24', plain,
% 0.48/0.64      (![X0 : $i]:
% 0.48/0.64         (r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_C_1))),
% 0.48/0.64      inference('demod', [status(thm)], ['22', '23'])).
% 0.48/0.64  thf('25', plain,
% 0.48/0.64      (![X11 : $i, X13 : $i]:
% 0.48/0.64         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.48/0.64      inference('cnf', [status(esa)], [t3_subset])).
% 0.48/0.64  thf('26', plain,
% 0.48/0.64      (![X0 : $i]:
% 0.48/0.64         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.48/0.64          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.48/0.64      inference('sup-', [status(thm)], ['24', '25'])).
% 0.48/0.64  thf('27', plain,
% 0.48/0.64      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.48/0.64         ((v1_relat_1 @ X21)
% 0.48/0.64          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.48/0.64      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.48/0.64  thf('28', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 0.48/0.64      inference('sup-', [status(thm)], ['26', '27'])).
% 0.48/0.64  thf('29', plain,
% 0.48/0.64      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X0)),
% 0.48/0.64      inference('demod', [status(thm)], ['15', '28'])).
% 0.48/0.64  thf('30', plain,
% 0.48/0.64      (![X0 : $i]:
% 0.48/0.64         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.48/0.64          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.48/0.64      inference('sup-', [status(thm)], ['24', '25'])).
% 0.48/0.64  thf(t13_relset_1, axiom,
% 0.48/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.64     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.48/0.64       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 0.48/0.64         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 0.48/0.64  thf('31', plain,
% 0.48/0.64      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.48/0.64         (~ (r1_tarski @ (k1_relat_1 @ X31) @ X32)
% 0.48/0.64          | (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.48/0.64          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33))))),
% 0.48/0.64      inference('cnf', [status(esa)], [t13_relset_1])).
% 0.48/0.64  thf('32', plain,
% 0.48/0.64      (![X0 : $i, X1 : $i]:
% 0.48/0.64         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.48/0.64           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C_1)))
% 0.48/0.64          | ~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X1))),
% 0.48/0.64      inference('sup-', [status(thm)], ['30', '31'])).
% 0.48/0.64  thf('33', plain,
% 0.48/0.64      (![X0 : $i]:
% 0.48/0.64         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.48/0.64          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_C_1)))),
% 0.48/0.64      inference('sup-', [status(thm)], ['29', '32'])).
% 0.48/0.64  thf('34', plain, ($false), inference('demod', [status(thm)], ['4', '33'])).
% 0.48/0.64  
% 0.48/0.64  % SZS output end Refutation
% 0.48/0.64  
% 0.48/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
