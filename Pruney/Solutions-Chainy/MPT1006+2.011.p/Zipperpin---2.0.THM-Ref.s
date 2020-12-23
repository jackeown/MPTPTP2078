%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QDaSgY5A0o

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   55 (  76 expanded)
%              Number of leaves         :   20 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :  280 ( 388 expanded)
%              Number of equality atoms :   21 (  35 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('1',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

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

thf('3',plain,(
    ( k8_relset_1 @ k1_xboole_0 @ sk_A_1 @ sk_C @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k8_relset_1 @ k1_xboole_0 @ sk_A_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( v1_xboole_0 @ ( k8_relset_1 @ k1_xboole_0 @ sk_A_1 @ sk_C @ sk_B ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(rc1_xboole_0,axiom,(
    ? [A: $i] :
      ( v1_xboole_0 @ A ) )).

thf('6',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('7',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('9',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,(
    ~ ( v1_xboole_0 @ ( k8_relset_1 @ k1_xboole_0 @ sk_A_1 @ sk_C @ sk_B ) ) ),
    inference('simplify_reflect+',[status(thm)],['5','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('14',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','14'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('16',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_xboole_0 @ X5 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('17',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['6','9'])).

thf('19',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('21',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( v1_xboole_0 @ ( k8_relset_1 @ k1_xboole_0 @ sk_A_1 @ k1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','21'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('23',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('24',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( m1_subset_1 @ ( k8_relset_1 @ X14 @ X15 @ X13 @ X16 ) @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relset_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('27',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('28',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X10 ) ) )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('29',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['6','9'])).

thf('31',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_xboole_0 @ ( k8_relset_1 @ k1_xboole_0 @ X1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,(
    $false ),
    inference(demod,[status(thm)],['22','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QDaSgY5A0o
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:35:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 84 iterations in 0.056s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.51  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.51  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.51  thf(l13_xboole_0, axiom,
% 0.21/0.51    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.51      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.51      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.51      inference('sup+', [status(thm)], ['0', '1'])).
% 0.21/0.51  thf(t60_funct_2, conjecture,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ k1_xboole_0 @ A ) & 
% 0.21/0.51         ( m1_subset_1 @
% 0.21/0.51           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) ) =>
% 0.21/0.51       ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.51        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ k1_xboole_0 @ A ) & 
% 0.21/0.51            ( m1_subset_1 @
% 0.21/0.51              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) ) =>
% 0.21/0.51          ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B ) = ( k1_xboole_0 ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t60_funct_2])).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (((k8_relset_1 @ k1_xboole_0 @ sk_A_1 @ sk_C @ sk_B) != (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((X0) != (k1_xboole_0))
% 0.21/0.51          | ~ (v1_xboole_0 @ X0)
% 0.21/0.51          | ~ (v1_xboole_0 @ (k8_relset_1 @ k1_xboole_0 @ sk_A_1 @ sk_C @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      ((~ (v1_xboole_0 @ (k8_relset_1 @ k1_xboole_0 @ sk_A_1 @ sk_C @ sk_B))
% 0.21/0.51        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.51  thf(rc1_xboole_0, axiom, (?[A:$i]: ( v1_xboole_0 @ A ))).
% 0.21/0.51  thf('6', plain, ((v1_xboole_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.21/0.51  thf('7', plain, ((v1_xboole_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.51      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.51  thf('9', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.51  thf('10', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.51      inference('demod', [status(thm)], ['6', '9'])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (~ (v1_xboole_0 @ (k8_relset_1 @ k1_xboole_0 @ sk_A_1 @ sk_C @ sk_B))),
% 0.21/0.51      inference('simplify_reflect+', [status(thm)], ['5', '10'])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ 
% 0.21/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_A_1)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t113_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.51       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (![X2 : $i, X3 : $i]:
% 0.21/0.51         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.51  thf('15', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.21/0.51      inference('demod', [status(thm)], ['12', '14'])).
% 0.21/0.51  thf(cc1_subset_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v1_xboole_0 @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (![X5 : $i, X6 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.21/0.51          | (v1_xboole_0 @ X5)
% 0.21/0.51          | ~ (v1_xboole_0 @ X6))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.21/0.51  thf('17', plain, ((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.51  thf('18', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.51      inference('demod', [status(thm)], ['6', '9'])).
% 0.21/0.51  thf('19', plain, ((v1_xboole_0 @ sk_C)),
% 0.21/0.51      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.51      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.51  thf('21', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (~ (v1_xboole_0 @ 
% 0.21/0.51          (k8_relset_1 @ k1_xboole_0 @ sk_A_1 @ k1_xboole_0 @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['11', '21'])).
% 0.21/0.51  thf(t4_subset_1, axiom,
% 0.21/0.51    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 0.21/0.51      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.51  thf(dt_k8_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.21/0.51          | (m1_subset_1 @ (k8_relset_1 @ X14 @ X15 @ X13 @ X16) @ 
% 0.21/0.51             (k1_zfmisc_1 @ X14)))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k8_relset_1])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (m1_subset_1 @ (k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2) @ 
% 0.21/0.51          (k1_zfmisc_1 @ X1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (![X2 : $i, X3 : $i]:
% 0.21/0.51         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.51  thf(cc4_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( v1_xboole_0 @ A ) =>
% 0.21/0.51       ( ![C:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.21/0.51           ( v1_xboole_0 @ C ) ) ) ))).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.51         (~ (v1_xboole_0 @ X10)
% 0.21/0.51          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X10)))
% 0.21/0.51          | (v1_xboole_0 @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (![X1 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.21/0.51          | (v1_xboole_0 @ X1)
% 0.21/0.51          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.51  thf('30', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.51      inference('demod', [status(thm)], ['6', '9'])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      (![X1 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.21/0.51          | (v1_xboole_0 @ X1))),
% 0.21/0.51      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (v1_xboole_0 @ (k8_relset_1 @ k1_xboole_0 @ X1 @ k1_xboole_0 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['25', '31'])).
% 0.21/0.51  thf('33', plain, ($false), inference('demod', [status(thm)], ['22', '32'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
