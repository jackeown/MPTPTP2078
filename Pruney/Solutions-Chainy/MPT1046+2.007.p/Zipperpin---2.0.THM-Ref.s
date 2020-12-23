%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dGlRXSzux2

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 168 expanded)
%              Number of leaves         :   13 (  56 expanded)
%              Depth                    :    9
%              Number of atoms          :  291 (2608 expanded)
%              Number of equality atoms :   27 ( 170 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k5_partfun1_type,type,(
    k5_partfun1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_partfun1_type,type,(
    k3_partfun1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['0','8','9'])).

thf('11',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( X3 != k1_xboole_0 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_funct_2 @ X4 @ X3 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X5 ) ) )
      | ( ( k5_partfun1 @ X3 @ X5 @ ( k3_partfun1 @ X4 @ X3 @ X5 ) )
        = ( k1_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t161_funct_2])).

thf('12',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k5_partfun1 @ k1_xboole_0 @ X5 @ ( k3_partfun1 @ X4 @ k1_xboole_0 @ X5 ) )
        = ( k1_tarski @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X5 ) ) )
      | ~ ( v1_funct_2 @ X4 @ k1_xboole_0 @ X5 )
      | ~ ( v1_funct_1 @ X4 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ k1_xboole_0 @ k1_xboole_0 )
    | ( ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ ( k3_partfun1 @ sk_B @ k1_xboole_0 @ k1_xboole_0 ) )
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('17',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('18',plain,(
    v1_funct_2 @ sk_B @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,
    ( ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ ( k3_partfun1 @ sk_B @ k1_xboole_0 @ k1_xboole_0 ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['13','14','18'])).

thf('20',plain,(
    ( k5_partfun1 @ sk_A @ sk_A @ ( k3_partfun1 @ sk_B @ sk_A @ sk_A ) )
 != ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('22',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('23',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('24',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('25',plain,(
    ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ ( k3_partfun1 @ sk_B @ k1_xboole_0 @ k1_xboole_0 ) )
 != ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['20','21','22','23','24'])).

thf('26',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['19','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dGlRXSzux2
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:08:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 12 iterations in 0.010s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.46  thf(k5_partfun1_type, type, k5_partfun1: $i > $i > $i > $i).
% 0.21/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(k3_partfun1_type, type, k3_partfun1: $i > $i > $i > $i).
% 0.21/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.46  thf(t162_funct_2, conjecture,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.46         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.46       ( ( k5_partfun1 @ A @ A @ ( k3_partfun1 @ B @ A @ A ) ) =
% 0.21/0.46         ( k1_tarski @ B ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i,B:$i]:
% 0.21/0.46        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.46            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.46          ( ( k5_partfun1 @ A @ A @ ( k3_partfun1 @ B @ A @ A ) ) =
% 0.21/0.46            ( k1_tarski @ B ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t162_funct_2])).
% 0.21/0.46  thf('0', plain,
% 0.21/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('1', plain,
% 0.21/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t161_funct_2, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.46         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.46       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.46         ( ( k5_partfun1 @ A @ B @ ( k3_partfun1 @ C @ A @ B ) ) =
% 0.21/0.46           ( k1_tarski @ C ) ) ) ))).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.46         (((X5) = (k1_xboole_0))
% 0.21/0.46          | ~ (v1_funct_1 @ X4)
% 0.21/0.46          | ~ (v1_funct_2 @ X4 @ X3 @ X5)
% 0.21/0.46          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X5)))
% 0.21/0.46          | ((k5_partfun1 @ X3 @ X5 @ (k3_partfun1 @ X4 @ X3 @ X5))
% 0.21/0.46              = (k1_tarski @ X4)))),
% 0.21/0.46      inference('cnf', [status(esa)], [t161_funct_2])).
% 0.21/0.46  thf('3', plain,
% 0.21/0.46      ((((k5_partfun1 @ sk_A @ sk_A @ (k3_partfun1 @ sk_B @ sk_A @ sk_A))
% 0.21/0.46          = (k1_tarski @ sk_B))
% 0.21/0.46        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.21/0.46        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.46        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.46  thf('4', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('5', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('6', plain,
% 0.21/0.46      ((((k5_partfun1 @ sk_A @ sk_A @ (k3_partfun1 @ sk_B @ sk_A @ sk_A))
% 0.21/0.46          = (k1_tarski @ sk_B))
% 0.21/0.46        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.46      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      (((k5_partfun1 @ sk_A @ sk_A @ (k3_partfun1 @ sk_B @ sk_A @ sk_A))
% 0.21/0.46         != (k1_tarski @ sk_B))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('8', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.46      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.21/0.46  thf('9', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.46      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.21/0.46  thf('10', plain,
% 0.21/0.46      ((m1_subset_1 @ sk_B @ 
% 0.21/0.46        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.21/0.46      inference('demod', [status(thm)], ['0', '8', '9'])).
% 0.21/0.46  thf('11', plain,
% 0.21/0.46      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.46         (((X3) != (k1_xboole_0))
% 0.21/0.46          | ~ (v1_funct_1 @ X4)
% 0.21/0.46          | ~ (v1_funct_2 @ X4 @ X3 @ X5)
% 0.21/0.46          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X5)))
% 0.21/0.46          | ((k5_partfun1 @ X3 @ X5 @ (k3_partfun1 @ X4 @ X3 @ X5))
% 0.21/0.46              = (k1_tarski @ X4)))),
% 0.21/0.46      inference('cnf', [status(esa)], [t161_funct_2])).
% 0.21/0.46  thf('12', plain,
% 0.21/0.46      (![X4 : $i, X5 : $i]:
% 0.21/0.46         (((k5_partfun1 @ k1_xboole_0 @ X5 @ 
% 0.21/0.46            (k3_partfun1 @ X4 @ k1_xboole_0 @ X5)) = (k1_tarski @ X4))
% 0.21/0.46          | ~ (m1_subset_1 @ X4 @ 
% 0.21/0.46               (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X5)))
% 0.21/0.46          | ~ (v1_funct_2 @ X4 @ k1_xboole_0 @ X5)
% 0.21/0.46          | ~ (v1_funct_1 @ X4))),
% 0.21/0.46      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.46  thf('13', plain,
% 0.21/0.46      ((~ (v1_funct_1 @ sk_B)
% 0.21/0.46        | ~ (v1_funct_2 @ sk_B @ k1_xboole_0 @ k1_xboole_0)
% 0.21/0.46        | ((k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 0.21/0.46            (k3_partfun1 @ sk_B @ k1_xboole_0 @ k1_xboole_0))
% 0.21/0.46            = (k1_tarski @ sk_B)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['10', '12'])).
% 0.21/0.46  thf('14', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('15', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('16', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.46      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.21/0.46  thf('17', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.46      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.21/0.46  thf('18', plain, ((v1_funct_2 @ sk_B @ k1_xboole_0 @ k1_xboole_0)),
% 0.21/0.46      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.21/0.46  thf('19', plain,
% 0.21/0.46      (((k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 0.21/0.46         (k3_partfun1 @ sk_B @ k1_xboole_0 @ k1_xboole_0)) = (k1_tarski @ sk_B))),
% 0.21/0.46      inference('demod', [status(thm)], ['13', '14', '18'])).
% 0.21/0.46  thf('20', plain,
% 0.21/0.46      (((k5_partfun1 @ sk_A @ sk_A @ (k3_partfun1 @ sk_B @ sk_A @ sk_A))
% 0.21/0.46         != (k1_tarski @ sk_B))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('21', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.46      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.21/0.46  thf('22', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.46      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.21/0.46  thf('23', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.46      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.21/0.46  thf('24', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.46      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.21/0.46  thf('25', plain,
% 0.21/0.46      (((k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 0.21/0.46         (k3_partfun1 @ sk_B @ k1_xboole_0 @ k1_xboole_0))
% 0.21/0.46         != (k1_tarski @ sk_B))),
% 0.21/0.46      inference('demod', [status(thm)], ['20', '21', '22', '23', '24'])).
% 0.21/0.46  thf('26', plain, ($false),
% 0.21/0.46      inference('simplify_reflect-', [status(thm)], ['19', '25'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
