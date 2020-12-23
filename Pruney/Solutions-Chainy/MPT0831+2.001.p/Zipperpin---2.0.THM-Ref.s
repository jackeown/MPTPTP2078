%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OmXD2okrgO

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:20 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   69 (  82 expanded)
%              Number of leaves         :   30 (  37 expanded)
%              Depth                    :   13
%              Number of atoms          :  450 ( 674 expanded)
%              Number of equality atoms :   23 (  24 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_relset_1_type,type,(
    k5_relset_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ( ( k5_relset_1 @ X44 @ X45 @ X43 @ X46 )
        = ( k7_relat_1 @ X43 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k5_relset_1 @ sk_B @ sk_A @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r2_relset_1 @ sk_B @ sk_A @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X37 @ X38 @ X39 ) @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('7',plain,(
    m1_subset_1 @ ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('9',plain,(
    r1_tarski @ ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) @ sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( ( k1_relset_1 @ X41 @ X42 @ X40 )
        = ( k1_relat_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('12',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['9','12'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('15',plain,
    ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_D ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t117_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ C @ B )
     => ( ( k4_xboole_0 @ A @ C )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) ) ) )).

thf('17',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ X3 @ X4 ) @ ( k3_xboole_0 @ X3 @ ( k4_xboole_0 @ X4 @ X5 ) ) ) )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t117_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ sk_B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_C @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C ) @ ( k4_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_D ) @ sk_C ) @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['15','20'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('22',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('23',plain,
    ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_D ) @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('25',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_C ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_C ),
    inference(simplify,[status(thm)],['25'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('27',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X32 ) @ X33 )
      | ( ( k7_relat_1 @ X32 @ X33 )
        = X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k7_relat_1 @ sk_D @ sk_C )
      = sk_D ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('30',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v1_relat_1 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('31',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k7_relat_1 @ sk_D @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['28','31'])).

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
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ( r2_relset_1 @ X48 @ X49 @ X47 @ X50 )
      | ( X47 != X50 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('35',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( r2_relset_1 @ X48 @ X49 @ X50 @ X50 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    r2_relset_1 @ sk_B @ sk_A @ sk_D @ sk_D ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['4','32','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OmXD2okrgO
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:05:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.37/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.60  % Solved by: fo/fo7.sh
% 0.37/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.60  % done 304 iterations in 0.157s
% 0.37/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.60  % SZS output start Refutation
% 0.37/0.60  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.37/0.60  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.37/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.60  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.37/0.60  thf(sk_D_type, type, sk_D: $i).
% 0.37/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.60  thf(k5_relset_1_type, type, k5_relset_1: $i > $i > $i > $i > $i).
% 0.37/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.60  thf(t34_relset_1, conjecture,
% 0.37/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.60     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.37/0.60       ( ( r1_tarski @ B @ C ) =>
% 0.37/0.60         ( r2_relset_1 @ B @ A @ ( k5_relset_1 @ B @ A @ D @ C ) @ D ) ) ))).
% 0.37/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.60    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.60        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.37/0.60          ( ( r1_tarski @ B @ C ) =>
% 0.37/0.60            ( r2_relset_1 @ B @ A @ ( k5_relset_1 @ B @ A @ D @ C ) @ D ) ) ) )),
% 0.37/0.60    inference('cnf.neg', [status(esa)], [t34_relset_1])).
% 0.37/0.60  thf('0', plain,
% 0.37/0.60      (~ (r2_relset_1 @ sk_B @ sk_A @ 
% 0.37/0.60          (k5_relset_1 @ sk_B @ sk_A @ sk_D @ sk_C) @ sk_D)),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('1', plain,
% 0.37/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf(redefinition_k5_relset_1, axiom,
% 0.37/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.60       ( ( k5_relset_1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.37/0.60  thf('2', plain,
% 0.37/0.60      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.37/0.60         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 0.37/0.60          | ((k5_relset_1 @ X44 @ X45 @ X43 @ X46) = (k7_relat_1 @ X43 @ X46)))),
% 0.37/0.60      inference('cnf', [status(esa)], [redefinition_k5_relset_1])).
% 0.37/0.60  thf('3', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         ((k5_relset_1 @ sk_B @ sk_A @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.37/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.60  thf('4', plain,
% 0.37/0.60      (~ (r2_relset_1 @ sk_B @ sk_A @ (k7_relat_1 @ sk_D @ sk_C) @ sk_D)),
% 0.37/0.60      inference('demod', [status(thm)], ['0', '3'])).
% 0.37/0.60  thf('5', plain,
% 0.37/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf(dt_k1_relset_1, axiom,
% 0.37/0.60    (![A:$i,B:$i,C:$i]:
% 0.37/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.60       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.37/0.60  thf('6', plain,
% 0.37/0.60      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.37/0.60         ((m1_subset_1 @ (k1_relset_1 @ X37 @ X38 @ X39) @ (k1_zfmisc_1 @ X37))
% 0.37/0.60          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 0.37/0.60      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.37/0.60  thf('7', plain,
% 0.37/0.60      ((m1_subset_1 @ (k1_relset_1 @ sk_B @ sk_A @ sk_D) @ (k1_zfmisc_1 @ sk_B))),
% 0.37/0.60      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.60  thf(t3_subset, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.60  thf('8', plain,
% 0.37/0.60      (![X20 : $i, X21 : $i]:
% 0.37/0.60         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.37/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.60  thf('9', plain, ((r1_tarski @ (k1_relset_1 @ sk_B @ sk_A @ sk_D) @ sk_B)),
% 0.37/0.60      inference('sup-', [status(thm)], ['7', '8'])).
% 0.37/0.60  thf('10', plain,
% 0.37/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf(redefinition_k1_relset_1, axiom,
% 0.37/0.60    (![A:$i,B:$i,C:$i]:
% 0.37/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.60       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.37/0.60  thf('11', plain,
% 0.37/0.60      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.37/0.60         (((k1_relset_1 @ X41 @ X42 @ X40) = (k1_relat_1 @ X40))
% 0.37/0.60          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42))))),
% 0.37/0.60      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.37/0.60  thf('12', plain,
% 0.37/0.60      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.37/0.60      inference('sup-', [status(thm)], ['10', '11'])).
% 0.37/0.60  thf('13', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B)),
% 0.37/0.60      inference('demod', [status(thm)], ['9', '12'])).
% 0.37/0.60  thf(l32_xboole_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.60  thf('14', plain,
% 0.37/0.60      (![X0 : $i, X2 : $i]:
% 0.37/0.60         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.37/0.60      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.37/0.60  thf('15', plain,
% 0.37/0.60      (((k4_xboole_0 @ (k1_relat_1 @ sk_D) @ sk_B) = (k1_xboole_0))),
% 0.37/0.60      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.60  thf('16', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf(t117_xboole_1, axiom,
% 0.37/0.60    (![A:$i,B:$i,C:$i]:
% 0.37/0.60     ( ( r1_tarski @ C @ B ) =>
% 0.37/0.60       ( ( k4_xboole_0 @ A @ C ) =
% 0.37/0.60         ( k2_xboole_0 @
% 0.37/0.60           ( k4_xboole_0 @ A @ B ) @ 
% 0.37/0.60           ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) ) ))).
% 0.37/0.60  thf('17', plain,
% 0.37/0.60      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.37/0.60         (((k4_xboole_0 @ X3 @ X5)
% 0.37/0.60            = (k2_xboole_0 @ (k4_xboole_0 @ X3 @ X4) @ 
% 0.37/0.60               (k3_xboole_0 @ X3 @ (k4_xboole_0 @ X4 @ X5))))
% 0.37/0.60          | ~ (r1_tarski @ X5 @ X4))),
% 0.37/0.60      inference('cnf', [status(esa)], [t117_xboole_1])).
% 0.37/0.60  thf('18', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         ((k4_xboole_0 @ X0 @ sk_B)
% 0.37/0.60           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ 
% 0.37/0.60              (k3_xboole_0 @ X0 @ (k4_xboole_0 @ sk_C @ sk_B))))),
% 0.37/0.60      inference('sup-', [status(thm)], ['16', '17'])).
% 0.37/0.60  thf(t7_xboole_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.37/0.60  thf('19', plain,
% 0.37/0.60      (![X13 : $i, X14 : $i]: (r1_tarski @ X13 @ (k2_xboole_0 @ X13 @ X14))),
% 0.37/0.60      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.37/0.60  thf('20', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C) @ (k4_xboole_0 @ X0 @ sk_B))),
% 0.37/0.60      inference('sup+', [status(thm)], ['18', '19'])).
% 0.37/0.60  thf('21', plain,
% 0.37/0.60      ((r1_tarski @ (k4_xboole_0 @ (k1_relat_1 @ sk_D) @ sk_C) @ k1_xboole_0)),
% 0.37/0.60      inference('sup+', [status(thm)], ['15', '20'])).
% 0.37/0.60  thf(t3_xboole_1, axiom,
% 0.37/0.60    (![A:$i]:
% 0.37/0.60     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.37/0.60  thf('22', plain,
% 0.37/0.60      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ k1_xboole_0))),
% 0.37/0.60      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.37/0.60  thf('23', plain,
% 0.37/0.60      (((k4_xboole_0 @ (k1_relat_1 @ sk_D) @ sk_C) = (k1_xboole_0))),
% 0.37/0.60      inference('sup-', [status(thm)], ['21', '22'])).
% 0.37/0.60  thf('24', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 0.37/0.60      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.37/0.60  thf('25', plain,
% 0.37/0.60      ((((k1_xboole_0) != (k1_xboole_0))
% 0.37/0.60        | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_C))),
% 0.37/0.60      inference('sup-', [status(thm)], ['23', '24'])).
% 0.37/0.60  thf('26', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_C)),
% 0.37/0.60      inference('simplify', [status(thm)], ['25'])).
% 0.37/0.60  thf(t97_relat_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( v1_relat_1 @ B ) =>
% 0.37/0.60       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.37/0.60         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.37/0.60  thf('27', plain,
% 0.37/0.60      (![X32 : $i, X33 : $i]:
% 0.37/0.60         (~ (r1_tarski @ (k1_relat_1 @ X32) @ X33)
% 0.37/0.60          | ((k7_relat_1 @ X32 @ X33) = (X32))
% 0.37/0.60          | ~ (v1_relat_1 @ X32))),
% 0.37/0.60      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.37/0.60  thf('28', plain,
% 0.37/0.60      ((~ (v1_relat_1 @ sk_D) | ((k7_relat_1 @ sk_D @ sk_C) = (sk_D)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['26', '27'])).
% 0.37/0.60  thf('29', plain,
% 0.37/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf(cc1_relset_1, axiom,
% 0.37/0.60    (![A:$i,B:$i,C:$i]:
% 0.37/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.60       ( v1_relat_1 @ C ) ))).
% 0.37/0.60  thf('30', plain,
% 0.37/0.60      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.37/0.60         ((v1_relat_1 @ X34)
% 0.37/0.60          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.37/0.60      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.37/0.60  thf('31', plain, ((v1_relat_1 @ sk_D)),
% 0.37/0.60      inference('sup-', [status(thm)], ['29', '30'])).
% 0.37/0.60  thf('32', plain, (((k7_relat_1 @ sk_D @ sk_C) = (sk_D))),
% 0.37/0.60      inference('demod', [status(thm)], ['28', '31'])).
% 0.37/0.60  thf('33', plain,
% 0.37/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf(redefinition_r2_relset_1, axiom,
% 0.37/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.60     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.37/0.60         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.60       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.37/0.60  thf('34', plain,
% 0.37/0.60      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 0.37/0.60         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 0.37/0.60          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 0.37/0.60          | (r2_relset_1 @ X48 @ X49 @ X47 @ X50)
% 0.37/0.60          | ((X47) != (X50)))),
% 0.37/0.60      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.37/0.60  thf('35', plain,
% 0.37/0.60      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.37/0.60         ((r2_relset_1 @ X48 @ X49 @ X50 @ X50)
% 0.37/0.60          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49))))),
% 0.37/0.60      inference('simplify', [status(thm)], ['34'])).
% 0.37/0.60  thf('36', plain, ((r2_relset_1 @ sk_B @ sk_A @ sk_D @ sk_D)),
% 0.37/0.60      inference('sup-', [status(thm)], ['33', '35'])).
% 0.37/0.60  thf('37', plain, ($false),
% 0.37/0.60      inference('demod', [status(thm)], ['4', '32', '36'])).
% 0.37/0.60  
% 0.37/0.60  % SZS output end Refutation
% 0.37/0.60  
% 0.37/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
