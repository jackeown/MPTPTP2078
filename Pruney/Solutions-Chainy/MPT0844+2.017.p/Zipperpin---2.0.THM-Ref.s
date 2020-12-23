%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iFRQ88wt7x

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:31 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   59 (  69 expanded)
%              Number of leaves         :   25 (  31 expanded)
%              Depth                    :   12
%              Number of atoms          :  369 ( 513 expanded)
%              Number of equality atoms :   28 (  38 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relset_1_type,type,(
    k5_relset_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t96_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ A @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('0',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k7_relat_1 @ X25 @ X26 )
        = ( k3_xboole_0 @ X25 @ ( k2_zfmisc_1 @ X26 @ ( k2_relat_1 @ X25 ) ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t96_relat_1])).

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

thf('1',plain,(
    r1_xboole_0 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    r1_xboole_0 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X18 @ X20 ) @ ( k3_xboole_0 @ X19 @ X21 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X18 @ X19 ) @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ X1 ) @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('10',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_zfmisc_1 @ X16 @ X17 )
        = k1_xboole_0 )
      | ( X16 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('11',plain,(
    ! [X17: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X17 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ X1 ) @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ X1 ) @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('16',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('17',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X9 @ X10 )
      | ( r1_xboole_0 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_D @ X0 )
      | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_D @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_D @ ( k2_zfmisc_1 @ sk_B @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k7_relat_1 @ sk_D @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['0','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('24',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v1_relat_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('25',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k7_relat_1 @ sk_D @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,(
    ( k5_relset_1 @ sk_C @ sk_A @ sk_D @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k5_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k5_relset_1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('29',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( ( k5_relset_1 @ X31 @ X32 @ X30 @ X33 )
        = ( k7_relat_1 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_relset_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k5_relset_1 @ sk_C @ sk_A @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ( k7_relat_1 @ sk_D @ sk_B )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['26','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iFRQ88wt7x
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:16:06 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.35  % Running portfolio for 600 s
% 0.21/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.21/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.39/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.56  % Solved by: fo/fo7.sh
% 0.39/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.56  % done 290 iterations in 0.097s
% 0.39/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.56  % SZS output start Refutation
% 0.39/0.56  thf(k5_relset_1_type, type, k5_relset_1: $i > $i > $i > $i > $i).
% 0.39/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.56  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.39/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.39/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.56  thf(sk_D_type, type, sk_D: $i).
% 0.39/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.56  thf(t96_relat_1, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( v1_relat_1 @ B ) =>
% 0.39/0.56       ( ( k7_relat_1 @ B @ A ) =
% 0.39/0.56         ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ A @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.39/0.56  thf('0', plain,
% 0.39/0.56      (![X25 : $i, X26 : $i]:
% 0.39/0.56         (((k7_relat_1 @ X25 @ X26)
% 0.39/0.56            = (k3_xboole_0 @ X25 @ (k2_zfmisc_1 @ X26 @ (k2_relat_1 @ X25))))
% 0.39/0.56          | ~ (v1_relat_1 @ X25))),
% 0.39/0.56      inference('cnf', [status(esa)], [t96_relat_1])).
% 0.39/0.56  thf(t55_relset_1, conjecture,
% 0.39/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.56     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.39/0.56       ( ( r1_xboole_0 @ B @ C ) =>
% 0.39/0.56         ( ( k5_relset_1 @ C @ A @ D @ B ) = ( k1_xboole_0 ) ) ) ))).
% 0.39/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.56    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.56        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.39/0.56          ( ( r1_xboole_0 @ B @ C ) =>
% 0.39/0.56            ( ( k5_relset_1 @ C @ A @ D @ B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.39/0.56    inference('cnf.neg', [status(esa)], [t55_relset_1])).
% 0.39/0.56  thf('1', plain, ((r1_xboole_0 @ sk_B @ sk_C)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(symmetry_r1_xboole_0, axiom,
% 0.39/0.56    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.39/0.56  thf('2', plain,
% 0.39/0.56      (![X3 : $i, X4 : $i]:
% 0.39/0.56         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.39/0.56      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.39/0.56  thf('3', plain, ((r1_xboole_0 @ sk_C @ sk_B)),
% 0.39/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.56  thf(d7_xboole_0, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.39/0.56       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.39/0.56  thf('4', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.39/0.56      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.39/0.56  thf('5', plain, (((k3_xboole_0 @ sk_C @ sk_B) = (k1_xboole_0))),
% 0.39/0.56      inference('sup-', [status(thm)], ['3', '4'])).
% 0.39/0.56  thf(t123_zfmisc_1, axiom,
% 0.39/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.56     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 0.39/0.56       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.39/0.56  thf('6', plain,
% 0.39/0.56      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.39/0.56         ((k2_zfmisc_1 @ (k3_xboole_0 @ X18 @ X20) @ (k3_xboole_0 @ X19 @ X21))
% 0.39/0.56           = (k3_xboole_0 @ (k2_zfmisc_1 @ X18 @ X19) @ 
% 0.39/0.56              (k2_zfmisc_1 @ X20 @ X21)))),
% 0.39/0.56      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.39/0.56  thf('7', plain,
% 0.39/0.56      (![X0 : $i, X2 : $i]:
% 0.39/0.56         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.39/0.56      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.39/0.56  thf('8', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.56         (((k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0))
% 0.39/0.56            != (k1_xboole_0))
% 0.39/0.56          | (r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ X1) @ (k2_zfmisc_1 @ X2 @ X0)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.56  thf('9', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         (((k2_zfmisc_1 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0))
% 0.39/0.56            != (k1_xboole_0))
% 0.39/0.56          | (r1_xboole_0 @ (k2_zfmisc_1 @ sk_C @ X1) @ 
% 0.39/0.56             (k2_zfmisc_1 @ sk_B @ X0)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['5', '8'])).
% 0.39/0.56  thf(t113_zfmisc_1, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.39/0.56       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.39/0.56  thf('10', plain,
% 0.39/0.56      (![X16 : $i, X17 : $i]:
% 0.39/0.56         (((k2_zfmisc_1 @ X16 @ X17) = (k1_xboole_0))
% 0.39/0.56          | ((X16) != (k1_xboole_0)))),
% 0.39/0.56      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.39/0.56  thf('11', plain,
% 0.39/0.56      (![X17 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X17) = (k1_xboole_0))),
% 0.39/0.56      inference('simplify', [status(thm)], ['10'])).
% 0.39/0.56  thf('12', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         (((k1_xboole_0) != (k1_xboole_0))
% 0.39/0.56          | (r1_xboole_0 @ (k2_zfmisc_1 @ sk_C @ X1) @ 
% 0.39/0.56             (k2_zfmisc_1 @ sk_B @ X0)))),
% 0.39/0.56      inference('demod', [status(thm)], ['9', '11'])).
% 0.39/0.56  thf('13', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         (r1_xboole_0 @ (k2_zfmisc_1 @ sk_C @ X1) @ (k2_zfmisc_1 @ sk_B @ X0))),
% 0.39/0.56      inference('simplify', [status(thm)], ['12'])).
% 0.39/0.56  thf('14', plain,
% 0.39/0.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(t3_subset, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.39/0.56  thf('15', plain,
% 0.39/0.56      (![X22 : $i, X23 : $i]:
% 0.39/0.56         ((r1_tarski @ X22 @ X23) | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 0.39/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.56  thf('16', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_C @ sk_A))),
% 0.39/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.39/0.56  thf(t63_xboole_1, axiom,
% 0.39/0.56    (![A:$i,B:$i,C:$i]:
% 0.39/0.56     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.39/0.56       ( r1_xboole_0 @ A @ C ) ))).
% 0.39/0.56  thf('17', plain,
% 0.39/0.56      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.39/0.56         (~ (r1_tarski @ X8 @ X9)
% 0.39/0.56          | ~ (r1_xboole_0 @ X9 @ X10)
% 0.39/0.56          | (r1_xboole_0 @ X8 @ X10))),
% 0.39/0.56      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.39/0.56  thf('18', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         ((r1_xboole_0 @ sk_D @ X0)
% 0.39/0.56          | ~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_A) @ X0))),
% 0.39/0.56      inference('sup-', [status(thm)], ['16', '17'])).
% 0.39/0.56  thf('19', plain,
% 0.39/0.56      (![X0 : $i]: (r1_xboole_0 @ sk_D @ (k2_zfmisc_1 @ sk_B @ X0))),
% 0.39/0.56      inference('sup-', [status(thm)], ['13', '18'])).
% 0.39/0.56  thf('20', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.39/0.56      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.39/0.56  thf('21', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         ((k3_xboole_0 @ sk_D @ (k2_zfmisc_1 @ sk_B @ X0)) = (k1_xboole_0))),
% 0.39/0.56      inference('sup-', [status(thm)], ['19', '20'])).
% 0.39/0.56  thf('22', plain,
% 0.39/0.56      ((((k7_relat_1 @ sk_D @ sk_B) = (k1_xboole_0)) | ~ (v1_relat_1 @ sk_D))),
% 0.39/0.56      inference('sup+', [status(thm)], ['0', '21'])).
% 0.39/0.56  thf('23', plain,
% 0.39/0.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(cc1_relset_1, axiom,
% 0.39/0.56    (![A:$i,B:$i,C:$i]:
% 0.39/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.56       ( v1_relat_1 @ C ) ))).
% 0.39/0.56  thf('24', plain,
% 0.39/0.56      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.39/0.56         ((v1_relat_1 @ X27)
% 0.39/0.56          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.39/0.56      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.39/0.56  thf('25', plain, ((v1_relat_1 @ sk_D)),
% 0.39/0.56      inference('sup-', [status(thm)], ['23', '24'])).
% 0.39/0.56  thf('26', plain, (((k7_relat_1 @ sk_D @ sk_B) = (k1_xboole_0))),
% 0.39/0.56      inference('demod', [status(thm)], ['22', '25'])).
% 0.39/0.56  thf('27', plain,
% 0.39/0.56      (((k5_relset_1 @ sk_C @ sk_A @ sk_D @ sk_B) != (k1_xboole_0))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('28', plain,
% 0.39/0.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(redefinition_k5_relset_1, axiom,
% 0.39/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.56       ( ( k5_relset_1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.39/0.56  thf('29', plain,
% 0.39/0.56      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.39/0.56         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.39/0.56          | ((k5_relset_1 @ X31 @ X32 @ X30 @ X33) = (k7_relat_1 @ X30 @ X33)))),
% 0.39/0.56      inference('cnf', [status(esa)], [redefinition_k5_relset_1])).
% 0.39/0.56  thf('30', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         ((k5_relset_1 @ sk_C @ sk_A @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.39/0.56      inference('sup-', [status(thm)], ['28', '29'])).
% 0.39/0.56  thf('31', plain, (((k7_relat_1 @ sk_D @ sk_B) != (k1_xboole_0))),
% 0.39/0.56      inference('demod', [status(thm)], ['27', '30'])).
% 0.39/0.56  thf('32', plain, ($false),
% 0.39/0.56      inference('simplify_reflect-', [status(thm)], ['26', '31'])).
% 0.39/0.56  
% 0.39/0.56  % SZS output end Refutation
% 0.39/0.56  
% 0.39/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
