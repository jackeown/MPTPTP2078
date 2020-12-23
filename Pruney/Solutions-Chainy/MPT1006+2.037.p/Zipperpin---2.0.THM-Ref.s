%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Y17hpJD93u

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   50 (  80 expanded)
%              Number of leaves         :   21 (  33 expanded)
%              Depth                    :   14
%              Number of atoms          :  338 ( 722 expanded)
%              Number of equality atoms :   27 (  45 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t60_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ k1_xboole_0 @ A )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) )
     => ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ k1_xboole_0 @ A )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) )
       => ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t60_funct_2])).

thf('0',plain,(
    ( k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('1',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['3'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t47_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r1_tarski @ ( k8_relset_1 @ A @ B @ D @ C ) @ A ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k8_relset_1 @ X17 @ X18 @ X19 @ X20 ) @ X17 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t47_funct_2])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_C )
      | ( r1_tarski @ ( k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0 ) @ k1_xboole_0 )
      = ( k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('14',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0 ) @ ( k4_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k4_xboole_0 @ ( k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0 ) @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['6','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0 ) @ k1_xboole_0 )
      = ( k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0 ) @ k1_xboole_0 )
      = ( k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_xboole_0 @ X14 @ X16 )
      | ( ( k4_xboole_0 @ X14 @ X16 )
       != X14 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0 )
       != ( k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0 ) )
      | ( r1_xboole_0 @ ( k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0 ) @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0 ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0 ) @ k1_xboole_0 )
      = ( k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('25',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','25'])).

thf('27',plain,(
    $false ),
    inference(simplify,[status(thm)],['26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Y17hpJD93u
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:03:09 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 41 iterations in 0.026s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.48  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.22/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.48  thf(t60_funct_2, conjecture,
% 0.22/0.48    (![A:$i,B:$i,C:$i]:
% 0.22/0.48     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ k1_xboole_0 @ A ) & 
% 0.22/0.48         ( m1_subset_1 @
% 0.22/0.48           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) ) =>
% 0.22/0.48       ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.48        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ k1_xboole_0 @ A ) & 
% 0.22/0.48            ( m1_subset_1 @
% 0.22/0.48              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) ) =>
% 0.22/0.48          ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B ) = ( k1_xboole_0 ) ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t60_funct_2])).
% 0.22/0.48  thf('0', plain,
% 0.22/0.48      (((k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ sk_B) != (k1_xboole_0))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(idempotence_k3_xboole_0, axiom,
% 0.22/0.48    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.22/0.48  thf('1', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.22/0.48      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.22/0.48  thf(d7_xboole_0, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.22/0.48       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.48  thf('2', plain,
% 0.22/0.48      (![X0 : $i, X2 : $i]:
% 0.22/0.48         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.22/0.48      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.22/0.48  thf('3', plain,
% 0.22/0.48      (![X0 : $i]: (((X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.48  thf('4', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.22/0.48      inference('simplify', [status(thm)], ['3'])).
% 0.22/0.48  thf(t83_xboole_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.48  thf('5', plain,
% 0.22/0.48      (![X14 : $i, X15 : $i]:
% 0.22/0.48         (((k4_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_xboole_0 @ X14 @ X15))),
% 0.22/0.48      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.22/0.48  thf('6', plain,
% 0.22/0.48      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.48  thf('7', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_A)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(t47_funct_2, axiom,
% 0.22/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.48     ( ( ( v1_funct_1 @ D ) & 
% 0.22/0.48         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.48       ( r1_tarski @ ( k8_relset_1 @ A @ B @ D @ C ) @ A ) ))).
% 0.22/0.48  thf('8', plain,
% 0.22/0.48      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.48         ((r1_tarski @ (k8_relset_1 @ X17 @ X18 @ X19 @ X20) @ X17)
% 0.22/0.48          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.22/0.48          | ~ (v1_funct_1 @ X19))),
% 0.22/0.48      inference('cnf', [status(esa)], [t47_funct_2])).
% 0.22/0.48  thf('9', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (v1_funct_1 @ sk_C)
% 0.22/0.48          | (r1_tarski @ (k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0) @ 
% 0.22/0.48             k1_xboole_0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.48  thf('10', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('11', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (r1_tarski @ (k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0) @ 
% 0.22/0.48          k1_xboole_0)),
% 0.22/0.48      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.48  thf(t28_xboole_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.48  thf('12', plain,
% 0.22/0.48      (![X6 : $i, X7 : $i]:
% 0.22/0.48         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.22/0.48      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.22/0.48  thf('13', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((k3_xboole_0 @ (k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0) @ 
% 0.22/0.48           k1_xboole_0) = (k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.48  thf(t49_xboole_1, axiom,
% 0.22/0.48    (![A:$i,B:$i,C:$i]:
% 0.22/0.48     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.22/0.48       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.22/0.48  thf('14', plain,
% 0.22/0.48      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.48         ((k3_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X10))
% 0.22/0.48           = (k4_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10))),
% 0.22/0.48      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.22/0.48  thf('15', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         ((k3_xboole_0 @ (k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0) @ 
% 0.22/0.48           (k4_xboole_0 @ k1_xboole_0 @ X1))
% 0.22/0.48           = (k4_xboole_0 @ (k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0) @ X1))),
% 0.22/0.48      inference('sup+', [status(thm)], ['13', '14'])).
% 0.22/0.48  thf('16', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((k3_xboole_0 @ (k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0) @ 
% 0.22/0.48           k1_xboole_0)
% 0.22/0.48           = (k4_xboole_0 @ (k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0) @ 
% 0.22/0.48              k1_xboole_0))),
% 0.22/0.48      inference('sup+', [status(thm)], ['6', '15'])).
% 0.22/0.48  thf('17', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((k3_xboole_0 @ (k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0) @ 
% 0.22/0.48           k1_xboole_0) = (k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.48  thf('18', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((k4_xboole_0 @ (k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0) @ 
% 0.22/0.48           k1_xboole_0) = (k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0))),
% 0.22/0.48      inference('sup+', [status(thm)], ['16', '17'])).
% 0.22/0.48  thf('19', plain,
% 0.22/0.48      (![X14 : $i, X16 : $i]:
% 0.22/0.48         ((r1_xboole_0 @ X14 @ X16) | ((k4_xboole_0 @ X14 @ X16) != (X14)))),
% 0.22/0.48      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.22/0.48  thf('20', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (((k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0)
% 0.22/0.48            != (k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0))
% 0.22/0.48          | (r1_xboole_0 @ (k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0) @ 
% 0.22/0.48             k1_xboole_0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.48  thf('21', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (r1_xboole_0 @ (k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0) @ 
% 0.22/0.48          k1_xboole_0)),
% 0.22/0.48      inference('simplify', [status(thm)], ['20'])).
% 0.22/0.48  thf('22', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.22/0.48      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.22/0.48  thf('23', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((k3_xboole_0 @ (k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0) @ 
% 0.22/0.48           k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.48  thf('24', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((k3_xboole_0 @ (k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0) @ 
% 0.22/0.48           k1_xboole_0) = (k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.48  thf('25', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((k1_xboole_0) = (k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0))),
% 0.22/0.48      inference('sup+', [status(thm)], ['23', '24'])).
% 0.22/0.48  thf('26', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.48      inference('demod', [status(thm)], ['0', '25'])).
% 0.22/0.48  thf('27', plain, ($false), inference('simplify', [status(thm)], ['26'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
