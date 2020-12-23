%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XVlrpQnwKM

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 176 expanded)
%              Number of leaves         :   14 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :  352 (2688 expanded)
%              Number of equality atoms :   36 ( 184 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k5_partfun1_type,type,(
    k5_partfun1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_partfun1_type,type,(
    k3_partfun1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t162_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k5_partfun1 @ A @ A @ ( k3_partfun1 @ B @ A @ A ) )
        = ( k1_tarski @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ( ( k5_partfun1 @ A @ A @ ( k3_partfun1 @ B @ A @ A ) )
          = ( k1_tarski @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t162_funct_2])).

thf('0',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t161_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( k5_partfun1 @ A @ B @ ( k3_partfun1 @ C @ A @ B ) )
          = ( k1_tarski @ C ) ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_funct_2 @ X4 @ X3 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X5 ) ) )
      | ( ( k5_partfun1 @ X3 @ X5 @ ( k3_partfun1 @ X4 @ X3 @ X5 ) )
        = ( k1_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t161_funct_2])).

thf('3',plain,
    ( ( ( k5_partfun1 @ sk_A @ sk_A @ ( k3_partfun1 @ sk_B @ sk_A @ sk_A ) )
      = ( k1_tarski @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( ( k5_partfun1 @ sk_A @ sk_A @ ( k3_partfun1 @ sk_B @ sk_A @ sk_A ) )
      = ( k1_tarski @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ( k5_partfun1 @ sk_A @ sk_A @ ( k3_partfun1 @ sk_B @ sk_A @ sk_A ) )
 != ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('9',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('10',plain,(
    v1_funct_2 @ sk_B @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['0','8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('13',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('14',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('15',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','12','13','15'])).

thf('17',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( X3 != k1_xboole_0 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_funct_2 @ X4 @ X3 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X5 ) ) )
      | ( ( k5_partfun1 @ X3 @ X5 @ ( k3_partfun1 @ X4 @ X3 @ X5 ) )
        = ( k1_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t161_funct_2])).

thf('18',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k5_partfun1 @ k1_xboole_0 @ X5 @ ( k3_partfun1 @ X4 @ k1_xboole_0 @ X5 ) )
        = ( k1_tarski @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X5 ) ) )
      | ~ ( v1_funct_2 @ X4 @ k1_xboole_0 @ X5 )
      | ~ ( v1_funct_1 @ X4 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('20',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k5_partfun1 @ k1_xboole_0 @ X5 @ ( k3_partfun1 @ X4 @ k1_xboole_0 @ X5 ) )
        = ( k1_tarski @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_funct_2 @ X4 @ k1_xboole_0 @ X5 )
      | ~ ( v1_funct_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_funct_2 @ sk_B @ k1_xboole_0 @ X0 )
      | ( ( k5_partfun1 @ k1_xboole_0 @ X0 @ ( k3_partfun1 @ sk_B @ k1_xboole_0 @ X0 ) )
        = ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_2 @ sk_B @ k1_xboole_0 @ X0 )
      | ( ( k5_partfun1 @ k1_xboole_0 @ X0 @ ( k3_partfun1 @ sk_B @ k1_xboole_0 @ X0 ) )
        = ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ ( k3_partfun1 @ sk_B @ k1_xboole_0 @ k1_xboole_0 ) )
    = ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['10','23'])).

thf('25',plain,(
    ( k5_partfun1 @ sk_A @ sk_A @ ( k3_partfun1 @ sk_B @ sk_A @ sk_A ) )
 != ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('27',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('28',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('29',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('30',plain,(
    ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ ( k3_partfun1 @ sk_B @ k1_xboole_0 @ k1_xboole_0 ) )
 != ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['25','26','27','28','29'])).

thf('31',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['24','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XVlrpQnwKM
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:54:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 14 iterations in 0.012s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.47  thf(k5_partfun1_type, type, k5_partfun1: $i > $i > $i > $i).
% 0.20/0.47  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.47  thf(k3_partfun1_type, type, k3_partfun1: $i > $i > $i > $i).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(t162_funct_2, conjecture,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.20/0.47         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.47       ( ( k5_partfun1 @ A @ A @ ( k3_partfun1 @ B @ A @ A ) ) =
% 0.20/0.47         ( k1_tarski @ B ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i]:
% 0.20/0.47        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.20/0.47            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.47          ( ( k5_partfun1 @ A @ A @ ( k3_partfun1 @ B @ A @ A ) ) =
% 0.20/0.47            ( k1_tarski @ B ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t162_funct_2])).
% 0.20/0.47  thf('0', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t161_funct_2, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.47         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.47       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.47         ( ( k5_partfun1 @ A @ B @ ( k3_partfun1 @ C @ A @ B ) ) =
% 0.20/0.47           ( k1_tarski @ C ) ) ) ))).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.47         (((X5) = (k1_xboole_0))
% 0.20/0.47          | ~ (v1_funct_1 @ X4)
% 0.20/0.47          | ~ (v1_funct_2 @ X4 @ X3 @ X5)
% 0.20/0.47          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X5)))
% 0.20/0.47          | ((k5_partfun1 @ X3 @ X5 @ (k3_partfun1 @ X4 @ X3 @ X5))
% 0.20/0.47              = (k1_tarski @ X4)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t161_funct_2])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      ((((k5_partfun1 @ sk_A @ sk_A @ (k3_partfun1 @ sk_B @ sk_A @ sk_A))
% 0.20/0.47          = (k1_tarski @ sk_B))
% 0.20/0.47        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.20/0.47        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.47        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.47  thf('4', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('5', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      ((((k5_partfun1 @ sk_A @ sk_A @ (k3_partfun1 @ sk_B @ sk_A @ sk_A))
% 0.20/0.47          = (k1_tarski @ sk_B))
% 0.20/0.47        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.47      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (((k5_partfun1 @ sk_A @ sk_A @ (k3_partfun1 @ sk_B @ sk_A @ sk_A))
% 0.20/0.47         != (k1_tarski @ sk_B))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('8', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.20/0.47  thf('9', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.20/0.47  thf('10', plain, ((v1_funct_2 @ sk_B @ k1_xboole_0 @ k1_xboole_0)),
% 0.20/0.47      inference('demod', [status(thm)], ['0', '8', '9'])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('12', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.20/0.47  thf('13', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.20/0.47  thf(t113_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.47       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X1 : $i, X2 : $i]:
% 0.20/0.47         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X1) != (k1_xboole_0)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.47  thf('16', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.20/0.47      inference('demod', [status(thm)], ['11', '12', '13', '15'])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.47         (((X3) != (k1_xboole_0))
% 0.20/0.47          | ~ (v1_funct_1 @ X4)
% 0.20/0.47          | ~ (v1_funct_2 @ X4 @ X3 @ X5)
% 0.20/0.47          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X5)))
% 0.20/0.47          | ((k5_partfun1 @ X3 @ X5 @ (k3_partfun1 @ X4 @ X3 @ X5))
% 0.20/0.47              = (k1_tarski @ X4)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t161_funct_2])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      (![X4 : $i, X5 : $i]:
% 0.20/0.47         (((k5_partfun1 @ k1_xboole_0 @ X5 @ 
% 0.20/0.47            (k3_partfun1 @ X4 @ k1_xboole_0 @ X5)) = (k1_tarski @ X4))
% 0.20/0.47          | ~ (m1_subset_1 @ X4 @ 
% 0.20/0.47               (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X5)))
% 0.20/0.47          | ~ (v1_funct_2 @ X4 @ k1_xboole_0 @ X5)
% 0.20/0.47          | ~ (v1_funct_1 @ X4))),
% 0.20/0.47      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      (![X4 : $i, X5 : $i]:
% 0.20/0.47         (((k5_partfun1 @ k1_xboole_0 @ X5 @ 
% 0.20/0.47            (k3_partfun1 @ X4 @ k1_xboole_0 @ X5)) = (k1_tarski @ X4))
% 0.20/0.47          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.20/0.47          | ~ (v1_funct_2 @ X4 @ k1_xboole_0 @ X5)
% 0.20/0.47          | ~ (v1_funct_1 @ X4))),
% 0.20/0.47      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (v1_funct_1 @ sk_B)
% 0.20/0.47          | ~ (v1_funct_2 @ sk_B @ k1_xboole_0 @ X0)
% 0.20/0.47          | ((k5_partfun1 @ k1_xboole_0 @ X0 @ 
% 0.20/0.47              (k3_partfun1 @ sk_B @ k1_xboole_0 @ X0)) = (k1_tarski @ sk_B)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['16', '20'])).
% 0.20/0.47  thf('22', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (v1_funct_2 @ sk_B @ k1_xboole_0 @ X0)
% 0.20/0.47          | ((k5_partfun1 @ k1_xboole_0 @ X0 @ 
% 0.20/0.47              (k3_partfun1 @ sk_B @ k1_xboole_0 @ X0)) = (k1_tarski @ sk_B)))),
% 0.20/0.47      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.47  thf('24', plain,
% 0.20/0.47      (((k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 0.20/0.47         (k3_partfun1 @ sk_B @ k1_xboole_0 @ k1_xboole_0)) = (k1_tarski @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['10', '23'])).
% 0.20/0.47  thf('25', plain,
% 0.20/0.47      (((k5_partfun1 @ sk_A @ sk_A @ (k3_partfun1 @ sk_B @ sk_A @ sk_A))
% 0.20/0.47         != (k1_tarski @ sk_B))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('26', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.20/0.47  thf('27', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.20/0.47  thf('28', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.20/0.47  thf('29', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.20/0.47  thf('30', plain,
% 0.20/0.47      (((k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 0.20/0.47         (k3_partfun1 @ sk_B @ k1_xboole_0 @ k1_xboole_0))
% 0.20/0.47         != (k1_tarski @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['25', '26', '27', '28', '29'])).
% 0.20/0.47  thf('31', plain, ($false),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['24', '30'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
