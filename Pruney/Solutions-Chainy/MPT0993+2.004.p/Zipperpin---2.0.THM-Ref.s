%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Q4drf3idB1

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   63 (  85 expanded)
%              Number of leaves         :   28 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  392 ( 820 expanded)
%              Number of equality atoms :   19 (  19 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t40_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ A @ C )
       => ( r2_relset_1 @ A @ B @ ( k2_partfun1 @ A @ B @ D @ C ) @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r1_tarski @ A @ C )
         => ( r2_relset_1 @ A @ B @ ( k2_partfun1 @ A @ B @ D @ C ) @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t40_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ( ( k2_partfun1 @ X25 @ X26 @ X24 @ X27 )
        = ( k7_relat_1 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('9',plain,(
    v4_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8
        = ( k7_relat_1 @ X8 @ X9 ) )
      | ~ ( v4_relat_1 @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('14',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['11','14'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('17',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k2_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k2_xboole_0 @ ( k1_relat_1 @ sk_D ) @ sk_A )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['12','13'])).

thf('21',plain,
    ( ( k2_xboole_0 @ ( k1_relat_1 @ sk_D ) @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['19','20'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('22',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_C ),
    inference('sup-',[status(thm)],['6','23'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('25',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ( ( k7_relat_1 @ X12 @ X13 )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k7_relat_1 @ sk_D @ sk_C )
      = sk_D ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['12','13'])).

thf('28',plain,
    ( ( k7_relat_1 @ sk_D @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('30',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( r2_relset_1 @ X21 @ X22 @ X20 @ X23 )
      | ( X20 != X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('31',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_relset_1 @ X21 @ X22 @ X23 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    $false ),
    inference(demod,[status(thm)],['0','5','28','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Q4drf3idB1
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:12:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 137 iterations in 0.060s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.52  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.52  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.21/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.21/0.52  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.52  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.52  thf(t40_funct_2, conjecture,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.52         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.52       ( ( r1_tarski @ A @ C ) =>
% 0.21/0.52         ( r2_relset_1 @ A @ B @ ( k2_partfun1 @ A @ B @ D @ C ) @ D ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.52            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.52          ( ( r1_tarski @ A @ C ) =>
% 0.21/0.52            ( r2_relset_1 @ A @ B @ ( k2_partfun1 @ A @ B @ D @ C ) @ D ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t40_funct_2])).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      (~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.21/0.52          (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_D)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(redefinition_k2_partfun1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52     ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.52       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.21/0.52          | ~ (v1_funct_1 @ X24)
% 0.21/0.52          | ((k2_partfun1 @ X25 @ X26 @ X24 @ X27) = (k7_relat_1 @ X24 @ X27)))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 0.21/0.52          | ~ (v1_funct_1 @ sk_D))),
% 0.21/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.52  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.21/0.52      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.52  thf('6', plain, ((r1_tarski @ sk_A @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(cc2_relset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.52       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.52         ((v4_relat_1 @ X17 @ X18)
% 0.21/0.52          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.21/0.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.52  thf('9', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 0.21/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.52  thf(t209_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.21/0.52       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (![X8 : $i, X9 : $i]:
% 0.21/0.52         (((X8) = (k7_relat_1 @ X8 @ X9))
% 0.21/0.52          | ~ (v4_relat_1 @ X8 @ X9)
% 0.21/0.52          | ~ (v1_relat_1 @ X8))),
% 0.21/0.52      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      ((~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(cc1_relset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.52       ( v1_relat_1 @ C ) ))).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.52         ((v1_relat_1 @ X14)
% 0.21/0.52          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.21/0.52      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.52  thf('14', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.52  thf('15', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['11', '14'])).
% 0.21/0.52  thf(t87_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ B ) =>
% 0.21/0.52       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i]:
% 0.21/0.52         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X10 @ X11)) @ X11)
% 0.21/0.52          | ~ (v1_relat_1 @ X10))),
% 0.21/0.52      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.21/0.52  thf(t12_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (![X6 : $i, X7 : $i]:
% 0.21/0.52         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.21/0.52      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X1)
% 0.21/0.52          | ((k2_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0) = (X0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      ((((k2_xboole_0 @ (k1_relat_1 @ sk_D) @ sk_A) = (sk_A))
% 0.21/0.52        | ~ (v1_relat_1 @ sk_D))),
% 0.21/0.52      inference('sup+', [status(thm)], ['15', '18'])).
% 0.21/0.52  thf('20', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.52  thf('21', plain, (((k2_xboole_0 @ (k1_relat_1 @ sk_D) @ sk_A) = (sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.52  thf(t11_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.52         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 0.21/0.52      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (r1_tarski @ sk_A @ X0) | (r1_tarski @ (k1_relat_1 @ sk_D) @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.52  thf('24', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_C)),
% 0.21/0.52      inference('sup-', [status(thm)], ['6', '23'])).
% 0.21/0.52  thf(t97_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ B ) =>
% 0.21/0.52       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.21/0.52         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      (![X12 : $i, X13 : $i]:
% 0.21/0.52         (~ (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.21/0.52          | ((k7_relat_1 @ X12 @ X13) = (X12))
% 0.21/0.52          | ~ (v1_relat_1 @ X12))),
% 0.21/0.52      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      ((~ (v1_relat_1 @ sk_D) | ((k7_relat_1 @ sk_D @ sk_C) = (sk_D)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.52  thf('27', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.52  thf('28', plain, (((k7_relat_1 @ sk_D @ sk_C) = (sk_D))),
% 0.21/0.52      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.52  thf('29', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(redefinition_r2_relset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.52         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.52       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.21/0.52  thf('30', plain,
% 0.21/0.52      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.21/0.52          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.21/0.52          | (r2_relset_1 @ X21 @ X22 @ X20 @ X23)
% 0.21/0.52          | ((X20) != (X23)))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.21/0.52  thf('31', plain,
% 0.21/0.52      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.52         ((r2_relset_1 @ X21 @ X22 @ X23 @ X23)
% 0.21/0.52          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.21/0.52      inference('simplify', [status(thm)], ['30'])).
% 0.21/0.52  thf('32', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D)),
% 0.21/0.52      inference('sup-', [status(thm)], ['29', '31'])).
% 0.21/0.52  thf('33', plain, ($false),
% 0.21/0.52      inference('demod', [status(thm)], ['0', '5', '28', '32'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
