%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uhnNypVR38

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:34 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   55 (  65 expanded)
%              Number of leaves         :   25 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :  308 ( 468 expanded)
%              Number of equality atoms :   14 (  24 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k5_relset_1_type,type,(
    k5_relset_1: $i > $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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

thf('0',plain,(
    ( k5_relset_1 @ sk_C @ sk_A @ sk_D @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k5_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k5_relset_1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( ( k5_relset_1 @ X21 @ X22 @ X20 @ X23 )
        = ( k7_relat_1 @ X20 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k5_relset_1 @ sk_C @ sk_A @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_xboole_0 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('6',plain,(
    r1_xboole_0 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X14 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('9',plain,(
    m1_subset_1 @ ( k1_relset_1 @ sk_C @ sk_A @ sk_D ) @ ( k1_zfmisc_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('12',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_D ) @ ( k1_zfmisc_1 @ sk_C ) ),
    inference(demod,[status(thm)],['9','12'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_C ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X4 )
      | ( r1_xboole_0 @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_D ) @ X0 )
      | ~ ( r1_xboole_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_D ) @ sk_B ),
    inference('sup-',[status(thm)],['6','17'])).

thf(t95_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('19',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X12 ) @ X13 )
      | ( ( k7_relat_1 @ X12 @ X13 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k7_relat_1 @ sk_D @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('24',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('25',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k7_relat_1 @ sk_D @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','25'])).

thf('27',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','3','26'])).

thf('28',plain,(
    $false ),
    inference(simplify,[status(thm)],['27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.08  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uhnNypVR38
% 0.08/0.27  % Computer   : n020.cluster.edu
% 0.08/0.27  % Model      : x86_64 x86_64
% 0.08/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.27  % Memory     : 8042.1875MB
% 0.08/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.27  % CPULimit   : 60
% 0.08/0.27  % DateTime   : Tue Dec  1 15:12:22 EST 2020
% 0.08/0.27  % CPUTime    : 
% 0.08/0.27  % Running portfolio for 600 s
% 0.08/0.27  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.27  % Number of cores: 8
% 0.12/0.27  % Python version: Python 3.6.8
% 0.12/0.27  % Running in FO mode
% 0.13/0.40  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.13/0.40  % Solved by: fo/fo7.sh
% 0.13/0.40  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.13/0.40  % done 30 iterations in 0.017s
% 0.13/0.40  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.13/0.40  % SZS output start Refutation
% 0.13/0.40  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.13/0.40  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.13/0.40  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.13/0.40  thf(sk_C_type, type, sk_C: $i).
% 0.13/0.40  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.13/0.40  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.13/0.40  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.13/0.40  thf(sk_D_type, type, sk_D: $i).
% 0.13/0.40  thf(k5_relset_1_type, type, k5_relset_1: $i > $i > $i > $i > $i).
% 0.13/0.40  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.13/0.40  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.13/0.40  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.13/0.40  thf(sk_A_type, type, sk_A: $i).
% 0.13/0.40  thf(sk_B_type, type, sk_B: $i).
% 0.13/0.40  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.13/0.40  thf(t55_relset_1, conjecture,
% 0.13/0.40    (![A:$i,B:$i,C:$i,D:$i]:
% 0.13/0.40     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.13/0.40       ( ( r1_xboole_0 @ B @ C ) =>
% 0.13/0.40         ( ( k5_relset_1 @ C @ A @ D @ B ) = ( k1_xboole_0 ) ) ) ))).
% 0.13/0.40  thf(zf_stmt_0, negated_conjecture,
% 0.13/0.40    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.13/0.40        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.13/0.40          ( ( r1_xboole_0 @ B @ C ) =>
% 0.13/0.40            ( ( k5_relset_1 @ C @ A @ D @ B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.13/0.40    inference('cnf.neg', [status(esa)], [t55_relset_1])).
% 0.13/0.40  thf('0', plain,
% 0.13/0.40      (((k5_relset_1 @ sk_C @ sk_A @ sk_D @ sk_B) != (k1_xboole_0))),
% 0.13/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.13/0.40  thf('1', plain,
% 0.13/0.40      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.13/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.13/0.40  thf(redefinition_k5_relset_1, axiom,
% 0.13/0.40    (![A:$i,B:$i,C:$i,D:$i]:
% 0.13/0.40     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.13/0.40       ( ( k5_relset_1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.13/0.40  thf('2', plain,
% 0.13/0.40      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.13/0.40         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.13/0.40          | ((k5_relset_1 @ X21 @ X22 @ X20 @ X23) = (k7_relat_1 @ X20 @ X23)))),
% 0.13/0.40      inference('cnf', [status(esa)], [redefinition_k5_relset_1])).
% 0.13/0.40  thf('3', plain,
% 0.13/0.40      (![X0 : $i]:
% 0.13/0.40         ((k5_relset_1 @ sk_C @ sk_A @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.13/0.40      inference('sup-', [status(thm)], ['1', '2'])).
% 0.13/0.40  thf('4', plain, ((r1_xboole_0 @ sk_B @ sk_C)),
% 0.13/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.13/0.40  thf(symmetry_r1_xboole_0, axiom,
% 0.13/0.40    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.13/0.40  thf('5', plain,
% 0.13/0.40      (![X0 : $i, X1 : $i]:
% 0.13/0.40         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.13/0.40      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.13/0.40  thf('6', plain, ((r1_xboole_0 @ sk_C @ sk_B)),
% 0.13/0.40      inference('sup-', [status(thm)], ['4', '5'])).
% 0.13/0.40  thf('7', plain,
% 0.13/0.40      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.13/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.13/0.40  thf(dt_k1_relset_1, axiom,
% 0.13/0.40    (![A:$i,B:$i,C:$i]:
% 0.13/0.40     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.13/0.40       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.13/0.40  thf('8', plain,
% 0.13/0.40      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.13/0.40         ((m1_subset_1 @ (k1_relset_1 @ X14 @ X15 @ X16) @ (k1_zfmisc_1 @ X14))
% 0.13/0.40          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.13/0.40      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.13/0.40  thf('9', plain,
% 0.13/0.40      ((m1_subset_1 @ (k1_relset_1 @ sk_C @ sk_A @ sk_D) @ (k1_zfmisc_1 @ sk_C))),
% 0.13/0.40      inference('sup-', [status(thm)], ['7', '8'])).
% 0.13/0.40  thf('10', plain,
% 0.13/0.40      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.13/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.13/0.40  thf(redefinition_k1_relset_1, axiom,
% 0.13/0.40    (![A:$i,B:$i,C:$i]:
% 0.13/0.40     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.13/0.40       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.13/0.40  thf('11', plain,
% 0.13/0.40      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.13/0.40         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 0.13/0.40          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.13/0.40      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.13/0.40  thf('12', plain,
% 0.13/0.40      (((k1_relset_1 @ sk_C @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.13/0.40      inference('sup-', [status(thm)], ['10', '11'])).
% 0.13/0.40  thf('13', plain,
% 0.13/0.40      ((m1_subset_1 @ (k1_relat_1 @ sk_D) @ (k1_zfmisc_1 @ sk_C))),
% 0.13/0.40      inference('demod', [status(thm)], ['9', '12'])).
% 0.13/0.40  thf(t3_subset, axiom,
% 0.13/0.40    (![A:$i,B:$i]:
% 0.13/0.40     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.13/0.40  thf('14', plain,
% 0.13/0.40      (![X5 : $i, X6 : $i]:
% 0.13/0.40         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.13/0.40      inference('cnf', [status(esa)], [t3_subset])).
% 0.13/0.40  thf('15', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_C)),
% 0.13/0.40      inference('sup-', [status(thm)], ['13', '14'])).
% 0.13/0.40  thf(t63_xboole_1, axiom,
% 0.13/0.40    (![A:$i,B:$i,C:$i]:
% 0.13/0.40     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.13/0.40       ( r1_xboole_0 @ A @ C ) ))).
% 0.13/0.40  thf('16', plain,
% 0.13/0.40      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.13/0.40         (~ (r1_tarski @ X2 @ X3)
% 0.13/0.40          | ~ (r1_xboole_0 @ X3 @ X4)
% 0.13/0.40          | (r1_xboole_0 @ X2 @ X4))),
% 0.13/0.40      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.13/0.40  thf('17', plain,
% 0.13/0.40      (![X0 : $i]:
% 0.13/0.40         ((r1_xboole_0 @ (k1_relat_1 @ sk_D) @ X0)
% 0.13/0.40          | ~ (r1_xboole_0 @ sk_C @ X0))),
% 0.13/0.40      inference('sup-', [status(thm)], ['15', '16'])).
% 0.13/0.40  thf('18', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_D) @ sk_B)),
% 0.13/0.40      inference('sup-', [status(thm)], ['6', '17'])).
% 0.13/0.40  thf(t95_relat_1, axiom,
% 0.13/0.40    (![A:$i,B:$i]:
% 0.13/0.40     ( ( v1_relat_1 @ B ) =>
% 0.13/0.40       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.13/0.40         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.13/0.40  thf('19', plain,
% 0.13/0.40      (![X12 : $i, X13 : $i]:
% 0.13/0.40         (~ (r1_xboole_0 @ (k1_relat_1 @ X12) @ X13)
% 0.13/0.40          | ((k7_relat_1 @ X12 @ X13) = (k1_xboole_0))
% 0.13/0.40          | ~ (v1_relat_1 @ X12))),
% 0.13/0.40      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.13/0.40  thf('20', plain,
% 0.13/0.40      ((~ (v1_relat_1 @ sk_D) | ((k7_relat_1 @ sk_D @ sk_B) = (k1_xboole_0)))),
% 0.13/0.40      inference('sup-', [status(thm)], ['18', '19'])).
% 0.13/0.40  thf('21', plain,
% 0.13/0.40      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.13/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.13/0.40  thf(cc2_relat_1, axiom,
% 0.13/0.40    (![A:$i]:
% 0.13/0.40     ( ( v1_relat_1 @ A ) =>
% 0.13/0.40       ( ![B:$i]:
% 0.13/0.40         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.13/0.40  thf('22', plain,
% 0.13/0.40      (![X8 : $i, X9 : $i]:
% 0.13/0.40         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.13/0.40          | (v1_relat_1 @ X8)
% 0.13/0.40          | ~ (v1_relat_1 @ X9))),
% 0.13/0.40      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.13/0.40  thf('23', plain,
% 0.13/0.40      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.13/0.40      inference('sup-', [status(thm)], ['21', '22'])).
% 0.13/0.40  thf(fc6_relat_1, axiom,
% 0.13/0.40    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.13/0.40  thf('24', plain,
% 0.13/0.40      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 0.13/0.40      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.13/0.40  thf('25', plain, ((v1_relat_1 @ sk_D)),
% 0.13/0.40      inference('demod', [status(thm)], ['23', '24'])).
% 0.13/0.40  thf('26', plain, (((k7_relat_1 @ sk_D @ sk_B) = (k1_xboole_0))),
% 0.13/0.40      inference('demod', [status(thm)], ['20', '25'])).
% 0.13/0.40  thf('27', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.13/0.40      inference('demod', [status(thm)], ['0', '3', '26'])).
% 0.13/0.40  thf('28', plain, ($false), inference('simplify', [status(thm)], ['27'])).
% 0.13/0.40  
% 0.13/0.40  % SZS output end Refutation
% 0.13/0.40  
% 0.13/0.41  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
