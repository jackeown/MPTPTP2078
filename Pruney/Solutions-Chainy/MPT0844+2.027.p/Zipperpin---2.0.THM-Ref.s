%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aa0cPIXijz

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:33 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   62 (  86 expanded)
%              Number of leaves         :   28 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :  332 ( 596 expanded)
%              Number of equality atoms :   18 (  30 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k5_relset_1_type,type,(
    k5_relset_1: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( ( k5_relset_1 @ X22 @ X23 @ X21 @ X24 )
        = ( k7_relat_1 @ X21 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k5_relset_1 @ sk_C @ sk_A @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v4_relat_1 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('6',plain,(
    v4_relat_1 @ sk_D @ sk_C ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14
        = ( k7_relat_1 @ X14 @ X15 ) )
      | ~ ( v4_relat_1 @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('8',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('13',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('15',plain,(
    r1_xboole_0 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X3 )
        = X2 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('17',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = sk_B ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('18',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_xboole_0 @ X5 @ ( k4_xboole_0 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ sk_C ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','22'])).

thf('24',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['14','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['11','12'])).

thf('26',plain,(
    r1_xboole_0 @ sk_B @ ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(t187_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) )
         => ( ( k7_relat_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf('27',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_xboole_0 @ X12 @ ( k1_relat_1 @ X13 ) )
      | ( ( k7_relat_1 @ X13 @ X12 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k7_relat_1 @ sk_D @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['11','12'])).

thf('30',plain,
    ( ( k7_relat_1 @ sk_D @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','3','30'])).

thf('32',plain,(
    $false ),
    inference(simplify,[status(thm)],['31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aa0cPIXijz
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:59:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.41/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.59  % Solved by: fo/fo7.sh
% 0.41/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.59  % done 105 iterations in 0.133s
% 0.41/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.59  % SZS output start Refutation
% 0.41/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.41/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.59  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.41/0.59  thf(sk_D_type, type, sk_D: $i).
% 0.41/0.59  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.41/0.59  thf(k5_relset_1_type, type, k5_relset_1: $i > $i > $i > $i > $i).
% 0.41/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.41/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.59  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.41/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.41/0.59  thf(t55_relset_1, conjecture,
% 0.41/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.59     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.41/0.59       ( ( r1_xboole_0 @ B @ C ) =>
% 0.41/0.59         ( ( k5_relset_1 @ C @ A @ D @ B ) = ( k1_xboole_0 ) ) ) ))).
% 0.41/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.59    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.59        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.41/0.59          ( ( r1_xboole_0 @ B @ C ) =>
% 0.41/0.59            ( ( k5_relset_1 @ C @ A @ D @ B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.41/0.59    inference('cnf.neg', [status(esa)], [t55_relset_1])).
% 0.41/0.59  thf('0', plain,
% 0.41/0.59      (((k5_relset_1 @ sk_C @ sk_A @ sk_D @ sk_B) != (k1_xboole_0))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('1', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(redefinition_k5_relset_1, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.59       ( ( k5_relset_1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.41/0.59  thf('2', plain,
% 0.41/0.59      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.41/0.59         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.41/0.59          | ((k5_relset_1 @ X22 @ X23 @ X21 @ X24) = (k7_relat_1 @ X21 @ X24)))),
% 0.41/0.59      inference('cnf', [status(esa)], [redefinition_k5_relset_1])).
% 0.41/0.59  thf('3', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((k5_relset_1 @ sk_C @ sk_A @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.41/0.59  thf('4', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(cc2_relset_1, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.59       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.41/0.59  thf('5', plain,
% 0.41/0.59      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.41/0.59         ((v4_relat_1 @ X18 @ X19)
% 0.41/0.59          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.41/0.59      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.41/0.59  thf('6', plain, ((v4_relat_1 @ sk_D @ sk_C)),
% 0.41/0.59      inference('sup-', [status(thm)], ['4', '5'])).
% 0.41/0.59  thf(t209_relat_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.41/0.59       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.41/0.59  thf('7', plain,
% 0.41/0.59      (![X14 : $i, X15 : $i]:
% 0.41/0.59         (((X14) = (k7_relat_1 @ X14 @ X15))
% 0.41/0.59          | ~ (v4_relat_1 @ X14 @ X15)
% 0.41/0.59          | ~ (v1_relat_1 @ X14))),
% 0.41/0.59      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.41/0.59  thf('8', plain,
% 0.41/0.59      ((~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ sk_C)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['6', '7'])).
% 0.41/0.59  thf('9', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(cc2_relat_1, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( v1_relat_1 @ A ) =>
% 0.41/0.59       ( ![B:$i]:
% 0.41/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.41/0.59  thf('10', plain,
% 0.41/0.59      (![X8 : $i, X9 : $i]:
% 0.41/0.59         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.41/0.59          | (v1_relat_1 @ X8)
% 0.41/0.59          | ~ (v1_relat_1 @ X9))),
% 0.41/0.59      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.41/0.59  thf('11', plain,
% 0.41/0.59      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.41/0.59      inference('sup-', [status(thm)], ['9', '10'])).
% 0.41/0.59  thf(fc6_relat_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.41/0.59  thf('12', plain,
% 0.41/0.59      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 0.41/0.59      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.41/0.59  thf('13', plain, ((v1_relat_1 @ sk_D)),
% 0.41/0.59      inference('demod', [status(thm)], ['11', '12'])).
% 0.41/0.59  thf('14', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_C))),
% 0.41/0.59      inference('demod', [status(thm)], ['8', '13'])).
% 0.41/0.59  thf('15', plain, ((r1_xboole_0 @ sk_B @ sk_C)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(t83_xboole_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.41/0.59  thf('16', plain,
% 0.41/0.59      (![X2 : $i, X3 : $i]:
% 0.41/0.59         (((k4_xboole_0 @ X2 @ X3) = (X2)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.41/0.59      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.41/0.59  thf('17', plain, (((k4_xboole_0 @ sk_B @ sk_C) = (sk_B))),
% 0.41/0.59      inference('sup-', [status(thm)], ['15', '16'])).
% 0.41/0.59  thf(t87_relat_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( v1_relat_1 @ B ) =>
% 0.41/0.59       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.41/0.59  thf('18', plain,
% 0.41/0.59      (![X16 : $i, X17 : $i]:
% 0.41/0.59         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X16 @ X17)) @ X17)
% 0.41/0.59          | ~ (v1_relat_1 @ X16))),
% 0.41/0.59      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.41/0.59  thf(t85_xboole_1, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.41/0.59  thf('19', plain,
% 0.41/0.59      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.41/0.59         (~ (r1_tarski @ X5 @ X6)
% 0.41/0.59          | (r1_xboole_0 @ X5 @ (k4_xboole_0 @ X7 @ X6)))),
% 0.41/0.59      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.41/0.59  thf('20', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.59         (~ (v1_relat_1 @ X1)
% 0.41/0.59          | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 0.41/0.59             (k4_xboole_0 @ X2 @ X0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['18', '19'])).
% 0.41/0.59  thf(symmetry_r1_xboole_0, axiom,
% 0.41/0.59    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.41/0.59  thf('21', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.41/0.59      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.41/0.59  thf('22', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.59         (~ (v1_relat_1 @ X2)
% 0.41/0.59          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 0.41/0.59             (k1_relat_1 @ (k7_relat_1 @ X2 @ X0))))),
% 0.41/0.59      inference('sup-', [status(thm)], ['20', '21'])).
% 0.41/0.59  thf('23', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((r1_xboole_0 @ sk_B @ (k1_relat_1 @ (k7_relat_1 @ X0 @ sk_C)))
% 0.41/0.59          | ~ (v1_relat_1 @ X0))),
% 0.41/0.59      inference('sup+', [status(thm)], ['17', '22'])).
% 0.41/0.59  thf('24', plain,
% 0.41/0.59      (((r1_xboole_0 @ sk_B @ (k1_relat_1 @ sk_D)) | ~ (v1_relat_1 @ sk_D))),
% 0.41/0.59      inference('sup+', [status(thm)], ['14', '23'])).
% 0.41/0.59  thf('25', plain, ((v1_relat_1 @ sk_D)),
% 0.41/0.59      inference('demod', [status(thm)], ['11', '12'])).
% 0.41/0.59  thf('26', plain, ((r1_xboole_0 @ sk_B @ (k1_relat_1 @ sk_D))),
% 0.41/0.59      inference('demod', [status(thm)], ['24', '25'])).
% 0.41/0.59  thf(t187_relat_1, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( v1_relat_1 @ A ) =>
% 0.41/0.59       ( ![B:$i]:
% 0.41/0.59         ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) ) =>
% 0.41/0.59           ( ( k7_relat_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.41/0.59  thf('27', plain,
% 0.41/0.59      (![X12 : $i, X13 : $i]:
% 0.41/0.59         (~ (r1_xboole_0 @ X12 @ (k1_relat_1 @ X13))
% 0.41/0.59          | ((k7_relat_1 @ X13 @ X12) = (k1_xboole_0))
% 0.41/0.59          | ~ (v1_relat_1 @ X13))),
% 0.41/0.59      inference('cnf', [status(esa)], [t187_relat_1])).
% 0.41/0.59  thf('28', plain,
% 0.41/0.59      ((~ (v1_relat_1 @ sk_D) | ((k7_relat_1 @ sk_D @ sk_B) = (k1_xboole_0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['26', '27'])).
% 0.41/0.59  thf('29', plain, ((v1_relat_1 @ sk_D)),
% 0.41/0.59      inference('demod', [status(thm)], ['11', '12'])).
% 0.41/0.59  thf('30', plain, (((k7_relat_1 @ sk_D @ sk_B) = (k1_xboole_0))),
% 0.41/0.59      inference('demod', [status(thm)], ['28', '29'])).
% 0.41/0.59  thf('31', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.41/0.59      inference('demod', [status(thm)], ['0', '3', '30'])).
% 0.41/0.59  thf('32', plain, ($false), inference('simplify', [status(thm)], ['31'])).
% 0.41/0.59  
% 0.41/0.59  % SZS output end Refutation
% 0.41/0.59  
% 0.41/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
