%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.V7ZMecM8Ia

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   63 (  83 expanded)
%              Number of leaves         :   24 (  35 expanded)
%              Depth                    :   12
%              Number of atoms          :  427 ( 725 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relset_1_type,type,(
    k5_relset_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t34_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ( r1_tarski @ B @ C )
       => ( r2_relset_1 @ B @ A @ ( k5_relset_1 @ B @ A @ D @ C ) @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
       => ( ( r1_tarski @ B @ C )
         => ( r2_relset_1 @ B @ A @ ( k5_relset_1 @ B @ A @ D @ C ) @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_relset_1])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_B @ sk_A @ ( k5_relset_1 @ sk_B @ sk_A @ sk_D @ sk_C ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
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
      ( ( k5_relset_1 @ sk_B @ sk_A @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t193_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ A ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) @ X9 ) ),
    inference(cnf,[status(esa)],[t193_relat_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( r1_tarski @ ( k1_relat_1 @ X12 ) @ ( k1_relat_1 @ X11 ) )
      | ~ ( r1_tarski @ X12 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('15',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('16',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t118_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X3 @ X5 ) @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ sk_B @ X0 ) @ ( k2_zfmisc_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('21',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','16','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_C ),
    inference('sup-',[status(thm)],['8','26'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('28',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ( ( k7_relat_1 @ X13 @ X14 )
        = X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k7_relat_1 @ sk_D @ sk_C )
      = sk_D ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['14','15'])).

thf('31',plain,
    ( ( k7_relat_1 @ sk_D @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( r2_relset_1 @ sk_B @ sk_A @ sk_D @ sk_D ) ),
    inference(demod,[status(thm)],['0','3','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('34',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( r2_relset_1 @ X23 @ X24 @ X22 @ X25 )
      | ( X22 != X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('35',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r2_relset_1 @ X23 @ X24 @ X25 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    r2_relset_1 @ sk_B @ sk_A @ sk_D @ sk_D ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['32','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.V7ZMecM8Ia
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:03:55 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.60  % Solved by: fo/fo7.sh
% 0.20/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.60  % done 164 iterations in 0.140s
% 0.20/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.60  % SZS output start Refutation
% 0.20/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.60  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.60  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.20/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.60  thf(k5_relset_1_type, type, k5_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.60  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.60  thf(t34_relset_1, conjecture,
% 0.20/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.60     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.20/0.60       ( ( r1_tarski @ B @ C ) =>
% 0.20/0.60         ( r2_relset_1 @ B @ A @ ( k5_relset_1 @ B @ A @ D @ C ) @ D ) ) ))).
% 0.20/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.60    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.60        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.20/0.60          ( ( r1_tarski @ B @ C ) =>
% 0.20/0.60            ( r2_relset_1 @ B @ A @ ( k5_relset_1 @ B @ A @ D @ C ) @ D ) ) ) )),
% 0.20/0.60    inference('cnf.neg', [status(esa)], [t34_relset_1])).
% 0.20/0.60  thf('0', plain,
% 0.20/0.60      (~ (r2_relset_1 @ sk_B @ sk_A @ 
% 0.20/0.60          (k5_relset_1 @ sk_B @ sk_A @ sk_D @ sk_C) @ sk_D)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('1', plain,
% 0.20/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf(redefinition_k5_relset_1, axiom,
% 0.20/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.60       ( ( k5_relset_1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.20/0.60  thf('2', plain,
% 0.20/0.60      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.60         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.20/0.60          | ((k5_relset_1 @ X19 @ X20 @ X18 @ X21) = (k7_relat_1 @ X18 @ X21)))),
% 0.20/0.60      inference('cnf', [status(esa)], [redefinition_k5_relset_1])).
% 0.20/0.60  thf('3', plain,
% 0.20/0.60      (![X0 : $i]:
% 0.20/0.60         ((k5_relset_1 @ sk_B @ sk_A @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.20/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.60  thf('4', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf(t193_relat_1, axiom,
% 0.20/0.60    (![A:$i,B:$i]: ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ A ))).
% 0.20/0.60  thf('5', plain,
% 0.20/0.60      (![X9 : $i, X10 : $i]:
% 0.20/0.60         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10)) @ X9)),
% 0.20/0.60      inference('cnf', [status(esa)], [t193_relat_1])).
% 0.20/0.60  thf(t1_xboole_1, axiom,
% 0.20/0.60    (![A:$i,B:$i,C:$i]:
% 0.20/0.60     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.20/0.60       ( r1_tarski @ A @ C ) ))).
% 0.20/0.60  thf('6', plain,
% 0.20/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.60         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.60          | ~ (r1_tarski @ X1 @ X2)
% 0.20/0.60          | (r1_tarski @ X0 @ X2))),
% 0.20/0.60      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.20/0.60  thf('7', plain,
% 0.20/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.60         ((r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X2)
% 0.20/0.60          | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.60      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.60  thf('8', plain,
% 0.20/0.60      (![X0 : $i]:
% 0.20/0.60         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ sk_B @ X0)) @ sk_C)),
% 0.20/0.60      inference('sup-', [status(thm)], ['4', '7'])).
% 0.20/0.60  thf('9', plain,
% 0.20/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf(t3_subset, axiom,
% 0.20/0.60    (![A:$i,B:$i]:
% 0.20/0.60     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.60  thf('10', plain,
% 0.20/0.60      (![X6 : $i, X7 : $i]:
% 0.20/0.60         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.20/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.60  thf('11', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_B @ sk_A))),
% 0.20/0.60      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.60  thf(t25_relat_1, axiom,
% 0.20/0.60    (![A:$i]:
% 0.20/0.60     ( ( v1_relat_1 @ A ) =>
% 0.20/0.60       ( ![B:$i]:
% 0.20/0.60         ( ( v1_relat_1 @ B ) =>
% 0.20/0.60           ( ( r1_tarski @ A @ B ) =>
% 0.20/0.60             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.20/0.60               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.20/0.60  thf('12', plain,
% 0.20/0.60      (![X11 : $i, X12 : $i]:
% 0.20/0.60         (~ (v1_relat_1 @ X11)
% 0.20/0.60          | (r1_tarski @ (k1_relat_1 @ X12) @ (k1_relat_1 @ X11))
% 0.20/0.60          | ~ (r1_tarski @ X12 @ X11)
% 0.20/0.60          | ~ (v1_relat_1 @ X12))),
% 0.20/0.60      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.20/0.60  thf('13', plain,
% 0.20/0.60      ((~ (v1_relat_1 @ sk_D)
% 0.20/0.60        | (r1_tarski @ (k1_relat_1 @ sk_D) @ 
% 0.20/0.60           (k1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.20/0.60        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.60  thf('14', plain,
% 0.20/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf(cc1_relset_1, axiom,
% 0.20/0.60    (![A:$i,B:$i,C:$i]:
% 0.20/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.60       ( v1_relat_1 @ C ) ))).
% 0.20/0.60  thf('15', plain,
% 0.20/0.60      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.60         ((v1_relat_1 @ X15)
% 0.20/0.60          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.20/0.60      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.60  thf('16', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.60      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.60  thf('17', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf(t118_zfmisc_1, axiom,
% 0.20/0.60    (![A:$i,B:$i,C:$i]:
% 0.20/0.60     ( ( r1_tarski @ A @ B ) =>
% 0.20/0.60       ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.20/0.60         ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 0.20/0.60  thf('18', plain,
% 0.20/0.60      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.60         (~ (r1_tarski @ X3 @ X4)
% 0.20/0.60          | (r1_tarski @ (k2_zfmisc_1 @ X3 @ X5) @ (k2_zfmisc_1 @ X4 @ X5)))),
% 0.20/0.60      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 0.20/0.60  thf('19', plain,
% 0.20/0.60      (![X0 : $i]:
% 0.20/0.60         (r1_tarski @ (k2_zfmisc_1 @ sk_B @ X0) @ (k2_zfmisc_1 @ sk_C @ X0))),
% 0.20/0.60      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.60  thf('20', plain,
% 0.20/0.60      (![X6 : $i, X8 : $i]:
% 0.20/0.60         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.20/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.60  thf('21', plain,
% 0.20/0.60      (![X0 : $i]:
% 0.20/0.60         (m1_subset_1 @ (k2_zfmisc_1 @ sk_B @ X0) @ 
% 0.20/0.60          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X0)))),
% 0.20/0.60      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.60  thf('22', plain,
% 0.20/0.60      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.60         ((v1_relat_1 @ X15)
% 0.20/0.60          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.20/0.60      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.60  thf('23', plain, (![X0 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ X0))),
% 0.20/0.60      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.60  thf('24', plain,
% 0.20/0.60      ((r1_tarski @ (k1_relat_1 @ sk_D) @ 
% 0.20/0.60        (k1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.60      inference('demod', [status(thm)], ['13', '16', '23'])).
% 0.20/0.60  thf('25', plain,
% 0.20/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.60         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.60          | ~ (r1_tarski @ X1 @ X2)
% 0.20/0.60          | (r1_tarski @ X0 @ X2))),
% 0.20/0.60      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.20/0.60  thf('26', plain,
% 0.20/0.60      (![X0 : $i]:
% 0.20/0.60         ((r1_tarski @ (k1_relat_1 @ sk_D) @ X0)
% 0.20/0.60          | ~ (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) @ X0))),
% 0.20/0.60      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.60  thf('27', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_C)),
% 0.20/0.60      inference('sup-', [status(thm)], ['8', '26'])).
% 0.20/0.60  thf(t97_relat_1, axiom,
% 0.20/0.60    (![A:$i,B:$i]:
% 0.20/0.60     ( ( v1_relat_1 @ B ) =>
% 0.20/0.60       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.20/0.60         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.20/0.60  thf('28', plain,
% 0.20/0.60      (![X13 : $i, X14 : $i]:
% 0.20/0.60         (~ (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 0.20/0.60          | ((k7_relat_1 @ X13 @ X14) = (X13))
% 0.20/0.60          | ~ (v1_relat_1 @ X13))),
% 0.20/0.60      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.20/0.60  thf('29', plain,
% 0.20/0.60      ((~ (v1_relat_1 @ sk_D) | ((k7_relat_1 @ sk_D @ sk_C) = (sk_D)))),
% 0.20/0.60      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.60  thf('30', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.60      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.60  thf('31', plain, (((k7_relat_1 @ sk_D @ sk_C) = (sk_D))),
% 0.20/0.60      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.60  thf('32', plain, (~ (r2_relset_1 @ sk_B @ sk_A @ sk_D @ sk_D)),
% 0.20/0.60      inference('demod', [status(thm)], ['0', '3', '31'])).
% 0.20/0.60  thf('33', plain,
% 0.20/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf(redefinition_r2_relset_1, axiom,
% 0.20/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.60     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.60         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.60       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.20/0.60  thf('34', plain,
% 0.20/0.60      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.60         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.20/0.60          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.20/0.60          | (r2_relset_1 @ X23 @ X24 @ X22 @ X25)
% 0.20/0.60          | ((X22) != (X25)))),
% 0.20/0.60      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.20/0.60  thf('35', plain,
% 0.20/0.60      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.60         ((r2_relset_1 @ X23 @ X24 @ X25 @ X25)
% 0.20/0.60          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.20/0.60      inference('simplify', [status(thm)], ['34'])).
% 0.20/0.60  thf('36', plain, ((r2_relset_1 @ sk_B @ sk_A @ sk_D @ sk_D)),
% 0.20/0.60      inference('sup-', [status(thm)], ['33', '35'])).
% 0.20/0.60  thf('37', plain, ($false), inference('demod', [status(thm)], ['32', '36'])).
% 0.20/0.60  
% 0.20/0.60  % SZS output end Refutation
% 0.20/0.60  
% 0.43/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
