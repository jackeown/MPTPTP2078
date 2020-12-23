%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KLbMebDXBx

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   31 (  37 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :  168 ( 263 expanded)
%              Number of equality atoms :   14 (  23 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('3',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t47_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r1_tarski @ ( k8_relset_1 @ A @ B @ D @ C ) @ A ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ ( k8_relset_1 @ X4 @ X5 @ X6 @ X7 ) @ X4 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t47_funct_2])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ( r1_tarski @ ( k8_relset_1 @ k1_xboole_0 @ X0 @ X1 @ X2 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k8_relset_1 @ k1_xboole_0 @ X1 @ sk_C @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k8_relset_1 @ k1_xboole_0 @ X1 @ sk_C @ X0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ k1_xboole_0 @ X1 @ sk_C @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','12'])).

thf('14',plain,(
    $false ),
    inference(simplify,[status(thm)],['13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KLbMebDXBx
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:38:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 13 iterations in 0.012s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.46  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.46  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.46  thf(t60_funct_2, conjecture,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ k1_xboole_0 @ A ) & 
% 0.21/0.46         ( m1_subset_1 @
% 0.21/0.46           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) ) =>
% 0.21/0.46       ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.46        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ k1_xboole_0 @ A ) & 
% 0.21/0.46            ( m1_subset_1 @
% 0.21/0.46              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) ) =>
% 0.21/0.46          ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B ) = ( k1_xboole_0 ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t60_funct_2])).
% 0.21/0.46  thf('0', plain,
% 0.21/0.46      (((k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ sk_B) != (k1_xboole_0))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('1', plain,
% 0.21/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_A)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t113_zfmisc_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.46       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      (![X2 : $i, X3 : $i]:
% 0.21/0.46         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.21/0.46      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.46  thf('3', plain,
% 0.21/0.46      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.21/0.46      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.46  thf('4', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.21/0.46      inference('demod', [status(thm)], ['1', '3'])).
% 0.21/0.46  thf('5', plain,
% 0.21/0.46      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.21/0.46      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.46  thf(t47_funct_2, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.46     ( ( ( v1_funct_1 @ D ) & 
% 0.21/0.46         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.46       ( r1_tarski @ ( k8_relset_1 @ A @ B @ D @ C ) @ A ) ))).
% 0.21/0.46  thf('6', plain,
% 0.21/0.46      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.46         ((r1_tarski @ (k8_relset_1 @ X4 @ X5 @ X6 @ X7) @ X4)
% 0.21/0.46          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5)))
% 0.21/0.46          | ~ (v1_funct_1 @ X6))),
% 0.21/0.46      inference('cnf', [status(esa)], [t47_funct_2])).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.21/0.46          | ~ (v1_funct_1 @ X1)
% 0.21/0.46          | (r1_tarski @ (k8_relset_1 @ k1_xboole_0 @ X0 @ X1 @ X2) @ 
% 0.21/0.46             k1_xboole_0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.46  thf('8', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         ((r1_tarski @ (k8_relset_1 @ k1_xboole_0 @ X1 @ sk_C @ X0) @ 
% 0.21/0.46           k1_xboole_0)
% 0.21/0.46          | ~ (v1_funct_1 @ sk_C))),
% 0.21/0.46      inference('sup-', [status(thm)], ['4', '7'])).
% 0.21/0.46  thf('9', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('10', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         (r1_tarski @ (k8_relset_1 @ k1_xboole_0 @ X1 @ sk_C @ X0) @ 
% 0.21/0.46          k1_xboole_0)),
% 0.21/0.46      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.46  thf(t3_xboole_1, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.46  thf('11', plain,
% 0.21/0.46      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.21/0.46      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.21/0.46  thf('12', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         ((k8_relset_1 @ k1_xboole_0 @ X1 @ sk_C @ X0) = (k1_xboole_0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.46  thf('13', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.46      inference('demod', [status(thm)], ['0', '12'])).
% 0.21/0.46  thf('14', plain, ($false), inference('simplify', [status(thm)], ['13'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
