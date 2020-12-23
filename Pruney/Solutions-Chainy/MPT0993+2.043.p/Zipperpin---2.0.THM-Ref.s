%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mhIhuOFunX

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:51 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   62 (  84 expanded)
%              Number of leaves         :   26 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :  399 ( 784 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ( ( k2_partfun1 @ X21 @ X22 @ X20 @ X23 )
        = ( k7_relat_1 @ X20 @ X23 ) ) ) ),
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

thf(t193_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ A ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) @ X10 ) ),
    inference(cnf,[status(esa)],[t193_relat_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('13',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( r1_tarski @ ( k1_relat_1 @ X13 ) @ ( k1_relat_1 @ X12 ) )
      | ~ ( r1_tarski @ X13 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('17',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('19',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('20',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('22',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_C ),
    inference('sup-',[status(thm)],['10','24'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('26',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X14 ) @ X15 )
      | ( ( k7_relat_1 @ X14 @ X15 )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k7_relat_1 @ sk_D @ sk_C )
      = sk_D ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['18','19'])).

thf('29',plain,
    ( ( k7_relat_1 @ sk_D @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('31',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( r2_relset_1 @ X16 @ X17 @ X18 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['31'])).

thf('33',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['0','5','29','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mhIhuOFunX
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:46:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.34/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.34/0.52  % Solved by: fo/fo7.sh
% 0.34/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.52  % done 117 iterations in 0.064s
% 0.34/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.34/0.52  % SZS output start Refutation
% 0.34/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.34/0.52  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.34/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.34/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.52  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.34/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.34/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.34/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.34/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.34/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.34/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.34/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.34/0.52  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.34/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.34/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.34/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.34/0.53  thf(t40_funct_2, conjecture,
% 0.34/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.34/0.53     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.34/0.53         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.34/0.53       ( ( r1_tarski @ A @ C ) =>
% 0.34/0.53         ( r2_relset_1 @ A @ B @ ( k2_partfun1 @ A @ B @ D @ C ) @ D ) ) ))).
% 0.34/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.53    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.34/0.53        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.34/0.53            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.34/0.53          ( ( r1_tarski @ A @ C ) =>
% 0.34/0.53            ( r2_relset_1 @ A @ B @ ( k2_partfun1 @ A @ B @ D @ C ) @ D ) ) ) )),
% 0.34/0.53    inference('cnf.neg', [status(esa)], [t40_funct_2])).
% 0.34/0.53  thf('0', plain,
% 0.34/0.53      (~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.34/0.53          (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_D)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('1', plain,
% 0.34/0.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(redefinition_k2_partfun1, axiom,
% 0.34/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.34/0.53     ( ( ( v1_funct_1 @ C ) & 
% 0.34/0.53         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.34/0.53       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.34/0.53  thf('2', plain,
% 0.34/0.53      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.34/0.53         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.34/0.53          | ~ (v1_funct_1 @ X20)
% 0.34/0.53          | ((k2_partfun1 @ X21 @ X22 @ X20 @ X23) = (k7_relat_1 @ X20 @ X23)))),
% 0.34/0.53      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.34/0.53  thf('3', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 0.34/0.53          | ~ (v1_funct_1 @ sk_D))),
% 0.34/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.34/0.53  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('5', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.34/0.53      inference('demod', [status(thm)], ['3', '4'])).
% 0.34/0.53  thf('6', plain, ((r1_tarski @ sk_A @ sk_C)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(t193_relat_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]: ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ A ))).
% 0.34/0.53  thf('7', plain,
% 0.34/0.53      (![X10 : $i, X11 : $i]:
% 0.34/0.53         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11)) @ X10)),
% 0.34/0.53      inference('cnf', [status(esa)], [t193_relat_1])).
% 0.34/0.53  thf(t1_xboole_1, axiom,
% 0.34/0.53    (![A:$i,B:$i,C:$i]:
% 0.34/0.53     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.34/0.53       ( r1_tarski @ A @ C ) ))).
% 0.34/0.53  thf('8', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.53         (~ (r1_tarski @ X0 @ X1)
% 0.34/0.53          | ~ (r1_tarski @ X1 @ X2)
% 0.34/0.53          | (r1_tarski @ X0 @ X2))),
% 0.34/0.53      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.34/0.53  thf('9', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.53         ((r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X2)
% 0.34/0.53          | ~ (r1_tarski @ X0 @ X2))),
% 0.34/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.34/0.53  thf('10', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ X0)) @ sk_C)),
% 0.34/0.53      inference('sup-', [status(thm)], ['6', '9'])).
% 0.34/0.53  thf('11', plain,
% 0.34/0.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(t3_subset, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.34/0.53  thf('12', plain,
% 0.34/0.53      (![X3 : $i, X4 : $i]:
% 0.34/0.53         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.34/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.34/0.53  thf('13', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.34/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.34/0.53  thf(t25_relat_1, axiom,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ( v1_relat_1 @ A ) =>
% 0.34/0.53       ( ![B:$i]:
% 0.34/0.53         ( ( v1_relat_1 @ B ) =>
% 0.34/0.53           ( ( r1_tarski @ A @ B ) =>
% 0.34/0.53             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.34/0.53               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.34/0.53  thf('14', plain,
% 0.34/0.53      (![X12 : $i, X13 : $i]:
% 0.34/0.53         (~ (v1_relat_1 @ X12)
% 0.34/0.53          | (r1_tarski @ (k1_relat_1 @ X13) @ (k1_relat_1 @ X12))
% 0.34/0.53          | ~ (r1_tarski @ X13 @ X12)
% 0.34/0.53          | ~ (v1_relat_1 @ X13))),
% 0.34/0.53      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.34/0.53  thf('15', plain,
% 0.34/0.53      ((~ (v1_relat_1 @ sk_D)
% 0.34/0.53        | (r1_tarski @ (k1_relat_1 @ sk_D) @ 
% 0.34/0.53           (k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.34/0.53        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.34/0.53  thf('16', plain,
% 0.34/0.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(cc2_relat_1, axiom,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ( v1_relat_1 @ A ) =>
% 0.34/0.53       ( ![B:$i]:
% 0.34/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.34/0.53  thf('17', plain,
% 0.34/0.53      (![X6 : $i, X7 : $i]:
% 0.34/0.53         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.34/0.53          | (v1_relat_1 @ X6)
% 0.34/0.53          | ~ (v1_relat_1 @ X7))),
% 0.34/0.53      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.34/0.53  thf('18', plain,
% 0.34/0.53      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 0.34/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.34/0.53  thf(fc6_relat_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.34/0.53  thf('19', plain,
% 0.34/0.53      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.34/0.53      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.34/0.53  thf('20', plain, ((v1_relat_1 @ sk_D)),
% 0.34/0.53      inference('demod', [status(thm)], ['18', '19'])).
% 0.34/0.53  thf('21', plain,
% 0.34/0.53      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.34/0.53      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.34/0.53  thf('22', plain,
% 0.34/0.53      ((r1_tarski @ (k1_relat_1 @ sk_D) @ 
% 0.34/0.53        (k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.34/0.53      inference('demod', [status(thm)], ['15', '20', '21'])).
% 0.34/0.53  thf('23', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.53         (~ (r1_tarski @ X0 @ X1)
% 0.34/0.53          | ~ (r1_tarski @ X1 @ X2)
% 0.34/0.53          | (r1_tarski @ X0 @ X2))),
% 0.34/0.53      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.34/0.53  thf('24', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         ((r1_tarski @ (k1_relat_1 @ sk_D) @ X0)
% 0.34/0.53          | ~ (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) @ X0))),
% 0.34/0.53      inference('sup-', [status(thm)], ['22', '23'])).
% 0.34/0.53  thf('25', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_C)),
% 0.34/0.53      inference('sup-', [status(thm)], ['10', '24'])).
% 0.34/0.53  thf(t97_relat_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( v1_relat_1 @ B ) =>
% 0.34/0.53       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.34/0.53         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.34/0.53  thf('26', plain,
% 0.34/0.53      (![X14 : $i, X15 : $i]:
% 0.34/0.53         (~ (r1_tarski @ (k1_relat_1 @ X14) @ X15)
% 0.34/0.53          | ((k7_relat_1 @ X14 @ X15) = (X14))
% 0.34/0.53          | ~ (v1_relat_1 @ X14))),
% 0.34/0.53      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.34/0.53  thf('27', plain,
% 0.34/0.53      ((~ (v1_relat_1 @ sk_D) | ((k7_relat_1 @ sk_D @ sk_C) = (sk_D)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['25', '26'])).
% 0.34/0.53  thf('28', plain, ((v1_relat_1 @ sk_D)),
% 0.34/0.53      inference('demod', [status(thm)], ['18', '19'])).
% 0.34/0.53  thf('29', plain, (((k7_relat_1 @ sk_D @ sk_C) = (sk_D))),
% 0.34/0.53      inference('demod', [status(thm)], ['27', '28'])).
% 0.34/0.53  thf('30', plain,
% 0.34/0.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(reflexivity_r2_relset_1, axiom,
% 0.34/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.34/0.53     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.34/0.53         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.34/0.53       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.34/0.53  thf('31', plain,
% 0.34/0.53      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.34/0.53         ((r2_relset_1 @ X16 @ X17 @ X18 @ X18)
% 0.34/0.53          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.34/0.53          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.34/0.53      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.34/0.53  thf('32', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.53         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.34/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.34/0.53      inference('condensation', [status(thm)], ['31'])).
% 0.34/0.53  thf('33', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D)),
% 0.34/0.53      inference('sup-', [status(thm)], ['30', '32'])).
% 0.34/0.53  thf('34', plain, ($false),
% 0.34/0.53      inference('demod', [status(thm)], ['0', '5', '29', '33'])).
% 0.34/0.53  
% 0.34/0.53  % SZS output end Refutation
% 0.34/0.53  
% 0.40/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
