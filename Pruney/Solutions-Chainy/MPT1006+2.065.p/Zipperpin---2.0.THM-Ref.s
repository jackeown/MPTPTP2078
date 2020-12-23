%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8MvoktfUEv

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   30 (  34 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :  176 ( 252 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t47_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r1_tarski @ ( k8_relset_1 @ A @ B @ D @ C ) @ A ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r1_tarski @ ( k8_relset_1 @ X7 @ X8 @ X9 @ X10 ) @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t47_funct_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_C )
      | ( r1_tarski @ ( k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t35_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) )
    <=> ( ( k3_zfmisc_1 @ A @ B @ C )
       != k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X0 @ X1 @ X3 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('7',plain,(
    ! [X1: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t49_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( r1_tarski @ A @ ( k3_zfmisc_1 @ A @ B @ C ) )
          & ~ ( r1_tarski @ A @ ( k3_zfmisc_1 @ B @ C @ A ) )
          & ~ ( r1_tarski @ A @ ( k3_zfmisc_1 @ C @ A @ B ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ ( k3_zfmisc_1 @ X5 @ X6 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t49_mcart_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','10'])).

thf('12',plain,(
    $false ),
    inference(simplify,[status(thm)],['11'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8MvoktfUEv
% 0.14/0.36  % Computer   : n023.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 19:16:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 19 iterations in 0.013s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.49  thf(t60_funct_2, conjecture,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ k1_xboole_0 @ A ) & 
% 0.21/0.49         ( m1_subset_1 @
% 0.21/0.49           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) ) =>
% 0.21/0.49       ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.49        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ k1_xboole_0 @ A ) & 
% 0.21/0.49            ( m1_subset_1 @
% 0.21/0.49              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) ) =>
% 0.21/0.49          ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B ) = ( k1_xboole_0 ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t60_funct_2])).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (((k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ sk_B) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t47_funct_2, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( ( v1_funct_1 @ D ) & 
% 0.21/0.49         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.49       ( r1_tarski @ ( k8_relset_1 @ A @ B @ D @ C ) @ A ) ))).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.49         ((r1_tarski @ (k8_relset_1 @ X7 @ X8 @ X9 @ X10) @ X7)
% 0.21/0.49          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 0.21/0.49          | ~ (v1_funct_1 @ X9))),
% 0.21/0.49      inference('cnf', [status(esa)], [t47_funct_2])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_funct_1 @ sk_C)
% 0.21/0.49          | (r1_tarski @ (k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0) @ 
% 0.21/0.49             k1_xboole_0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.49  thf('4', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (r1_tarski @ (k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0) @ 
% 0.21/0.49          k1_xboole_0)),
% 0.21/0.49      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.49  thf(t35_mcart_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49         ( ( C ) != ( k1_xboole_0 ) ) ) <=>
% 0.21/0.49       ( ( k3_zfmisc_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) ))).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.21/0.49         (((X0) != (k1_xboole_0))
% 0.21/0.49          | ((k3_zfmisc_1 @ X0 @ X1 @ X3) = (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X1 : $i, X3 : $i]:
% 0.21/0.49         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X3) = (k1_xboole_0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.49  thf(t49_mcart_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ~( ( ~( r1_tarski @ A @ ( k3_zfmisc_1 @ A @ B @ C ) ) ) & 
% 0.21/0.49            ( ~( r1_tarski @ A @ ( k3_zfmisc_1 @ B @ C @ A ) ) ) & 
% 0.21/0.49            ( ~( r1_tarski @ A @ ( k3_zfmisc_1 @ C @ A @ B ) ) ) ) ) =>
% 0.21/0.49       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.49         (((X4) = (k1_xboole_0))
% 0.21/0.49          | ~ (r1_tarski @ X4 @ (k3_zfmisc_1 @ X5 @ X6 @ X4)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t49_mcart_1])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ X0) = (k1_xboole_0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['5', '9'])).
% 0.21/0.49  thf('11', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.49      inference('demod', [status(thm)], ['0', '10'])).
% 0.21/0.49  thf('12', plain, ($false), inference('simplify', [status(thm)], ['11'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
