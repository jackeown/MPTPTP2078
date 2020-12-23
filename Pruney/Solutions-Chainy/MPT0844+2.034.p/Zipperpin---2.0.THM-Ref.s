%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wL2BR0pA6T

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:34 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   61 (  83 expanded)
%              Number of leaves         :   24 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :  434 ( 762 expanded)
%              Number of equality atoms :   21 (  41 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relset_1_type,type,(
    k5_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t55_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
     => ( ( r1_xboole_0 @ B @ C )
       => ( ( k5_relset_1 @ C @ A @ D @ B )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
       => ( ( r1_xboole_0 @ B @ C )
         => ( ( k5_relset_1 @ C @ A @ D @ B )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t55_relset_1])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t34_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ( r1_tarski @ B @ C )
       => ( r2_relset_1 @ B @ A @ ( k5_relset_1 @ B @ A @ D @ C ) @ D ) ) ) )).

thf('3',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X27 ) ) )
      | ( r2_relset_1 @ X24 @ X27 @ ( k5_relset_1 @ X24 @ X27 @ X26 @ X25 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[t34_relset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_relset_1 @ sk_C @ sk_A @ ( k5_relset_1 @ sk_C @ sk_A @ sk_D @ X0 ) @ sk_D )
      | ~ ( r1_tarski @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k5_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k5_relset_1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( ( k5_relset_1 @ X13 @ X14 @ X12 @ X15 )
        = ( k7_relat_1 @ X12 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_relset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k5_relset_1 @ sk_C @ sk_A @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_relset_1 @ sk_C @ sk_A @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_D )
      | ~ ( r1_tarski @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('9',plain,(
    r2_relset_1 @ sk_C @ sk_A @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_D ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t33_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( m1_subset_1 @ ( k5_relset_1 @ A @ C @ D @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('11',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( m1_subset_1 @ ( k5_relset_1 @ X20 @ X21 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[t33_relset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k5_relset_1 @ sk_C @ sk_A @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k5_relset_1 @ sk_C @ sk_A @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('14',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('15',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( X16 = X19 )
      | ~ ( r2_relset_1 @ X17 @ X18 @ X16 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ X0 @ sk_A @ ( k7_relat_1 @ sk_D @ X0 ) @ X1 )
      | ( ( k7_relat_1 @ sk_D @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) )
    | ( ( k7_relat_1 @ sk_D @ sk_C )
      = sk_D ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k7_relat_1 @ sk_D @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    r1_xboole_0 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('22',plain,(
    r1_xboole_0 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t207_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_xboole_0 @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = k1_xboole_0 ) ) ) )).

thf('23',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_xboole_0 @ X9 @ X10 )
      | ~ ( v1_relat_1 @ X11 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X11 @ X9 ) @ X10 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t207_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ sk_C ) @ sk_B )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k7_relat_1 @ sk_D @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['19','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('27',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('29',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('30',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k7_relat_1 @ sk_D @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['25','30'])).

thf('32',plain,(
    ( k5_relset_1 @ sk_C @ sk_A @ sk_D @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k5_relset_1 @ sk_C @ sk_A @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('34',plain,(
    ( k7_relat_1 @ sk_D @ sk_B )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['31','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wL2BR0pA6T
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:04:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 76 iterations in 0.039s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(k5_relset_1_type, type, k5_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.50  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.50  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.20/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.50  thf(d10_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.50  thf('1', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.20/0.50      inference('simplify', [status(thm)], ['0'])).
% 0.20/0.50  thf(t55_relset_1, conjecture,
% 0.20/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.20/0.50       ( ( r1_xboole_0 @ B @ C ) =>
% 0.20/0.50         ( ( k5_relset_1 @ C @ A @ D @ B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.20/0.50          ( ( r1_xboole_0 @ B @ C ) =>
% 0.20/0.50            ( ( k5_relset_1 @ C @ A @ D @ B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t55_relset_1])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t34_relset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.20/0.50       ( ( r1_tarski @ B @ C ) =>
% 0.20/0.50         ( r2_relset_1 @ B @ A @ ( k5_relset_1 @ B @ A @ D @ C ) @ D ) ) ))).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.50         (~ (r1_tarski @ X24 @ X25)
% 0.20/0.50          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X27)))
% 0.20/0.50          | (r2_relset_1 @ X24 @ X27 @ (k5_relset_1 @ X24 @ X27 @ X26 @ X25) @ 
% 0.20/0.50             X26))),
% 0.20/0.50      inference('cnf', [status(esa)], [t34_relset_1])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r2_relset_1 @ sk_C @ sk_A @ 
% 0.20/0.50           (k5_relset_1 @ sk_C @ sk_A @ sk_D @ X0) @ sk_D)
% 0.20/0.50          | ~ (r1_tarski @ sk_C @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(redefinition_k5_relset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.50       ( ( k5_relset_1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.20/0.50          | ((k5_relset_1 @ X13 @ X14 @ X12 @ X15) = (k7_relat_1 @ X12 @ X15)))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k5_relset_1])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((k5_relset_1 @ sk_C @ sk_A @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r2_relset_1 @ sk_C @ sk_A @ (k7_relat_1 @ sk_D @ X0) @ sk_D)
% 0.20/0.50          | ~ (r1_tarski @ sk_C @ X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['4', '7'])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      ((r2_relset_1 @ sk_C @ sk_A @ (k7_relat_1 @ sk_D @ sk_C) @ sk_D)),
% 0.20/0.50      inference('sup-', [status(thm)], ['1', '8'])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t33_relset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.20/0.50       ( m1_subset_1 @
% 0.20/0.50         ( k5_relset_1 @ A @ C @ D @ B ) @ 
% 0.20/0.50         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.50         ((m1_subset_1 @ (k5_relset_1 @ X20 @ X21 @ X22 @ X23) @ 
% 0.20/0.50           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X21)))
% 0.20/0.50          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.20/0.50      inference('cnf', [status(esa)], [t33_relset_1])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (m1_subset_1 @ (k5_relset_1 @ sk_C @ sk_A @ sk_D @ X0) @ 
% 0.20/0.50          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((k5_relset_1 @ sk_C @ sk_A @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.20/0.50          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.50  thf(redefinition_r2_relset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.50         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.50       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.20/0.50          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.20/0.50          | ((X16) = (X19))
% 0.20/0.50          | ~ (r2_relset_1 @ X17 @ X18 @ X16 @ X19))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (r2_relset_1 @ X0 @ sk_A @ (k7_relat_1 @ sk_D @ X0) @ X1)
% 0.20/0.50          | ((k7_relat_1 @ sk_D @ X0) = (X1))
% 0.20/0.50          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))
% 0.20/0.50        | ((k7_relat_1 @ sk_D @ sk_C) = (sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['9', '16'])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('19', plain, (((k7_relat_1 @ sk_D @ sk_C) = (sk_D))),
% 0.20/0.50      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.50  thf('20', plain, ((r1_xboole_0 @ sk_B @ sk_C)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(symmetry_r1_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.50  thf('22', plain, ((r1_xboole_0 @ sk_C @ sk_B)),
% 0.20/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.50  thf(t207_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ C ) =>
% 0.20/0.50       ( ( r1_xboole_0 @ A @ B ) =>
% 0.20/0.50         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.50         (~ (r1_xboole_0 @ X9 @ X10)
% 0.20/0.50          | ~ (v1_relat_1 @ X11)
% 0.20/0.50          | ((k7_relat_1 @ (k7_relat_1 @ X11 @ X9) @ X10) = (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t207_relat_1])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k7_relat_1 @ (k7_relat_1 @ X0 @ sk_C) @ sk_B) = (k1_xboole_0))
% 0.20/0.50          | ~ (v1_relat_1 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      ((((k7_relat_1 @ sk_D @ sk_B) = (k1_xboole_0)) | ~ (v1_relat_1 @ sk_D))),
% 0.20/0.50      inference('sup+', [status(thm)], ['19', '24'])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(cc2_relat_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (![X5 : $i, X6 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.20/0.50          | (v1_relat_1 @ X5)
% 0.20/0.50          | ~ (v1_relat_1 @ X6))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.20/0.50      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.50  thf(fc6_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.50  thf('30', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.50      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.50  thf('31', plain, (((k7_relat_1 @ sk_D @ sk_B) = (k1_xboole_0))),
% 0.20/0.50      inference('demod', [status(thm)], ['25', '30'])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      (((k5_relset_1 @ sk_C @ sk_A @ sk_D @ sk_B) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((k5_relset_1 @ sk_C @ sk_A @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.50  thf('34', plain, (((k7_relat_1 @ sk_D @ sk_B) != (k1_xboole_0))),
% 0.20/0.50      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.50  thf('35', plain, ($false),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['31', '34'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
