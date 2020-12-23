%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qE4tDyAmhn

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 106 expanded)
%              Number of leaves         :   19 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :  277 (1266 expanded)
%              Number of equality atoms :   29 (  93 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t65_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( k1_funct_1 @ D @ C )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
       => ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ D @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('2',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( r2_hidden @ X46 @ X47 )
      | ( X48 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X47 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X49 @ X46 ) @ X48 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_C_1 ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('8',plain,(
    ! [X44: $i,X45: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X44 ) @ ( k1_tarski @ X45 ) )
        = ( k1_tarski @ X44 ) )
      | ( X44 = X45 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('9',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( r2_hidden @ X40 @ X41 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X40 ) @ X41 )
       != ( k1_tarski @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( X0 = X1 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ X1 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_funct_1 @ sk_D_1 @ sk_C_1 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,(
    ( k1_funct_1 @ sk_D_1 @ sk_C_1 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X43: $i,X44: $i] :
      ( ( X44 != X43 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X44 ) @ ( k1_tarski @ X43 ) )
       != ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('16',plain,(
    ! [X43: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X43 ) @ ( k1_tarski @ X43 ) )
     != ( k1_tarski @ X43 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
 != ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('19',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('20',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('21',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['17','18','19','20'])).

thf('22',plain,(
    $false ),
    inference(simplify,[status(thm)],['21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qE4tDyAmhn
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:30:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 78 iterations in 0.036s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.48  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.48  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(t65_funct_2, conjecture,
% 0.21/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.21/0.48         ( m1_subset_1 @
% 0.21/0.48           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.21/0.48       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.21/0.48            ( m1_subset_1 @
% 0.21/0.48              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.21/0.48          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.21/0.48  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_D_1 @ 
% 0.21/0.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t7_funct_2, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.48         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.48       ( ( r2_hidden @ C @ A ) =>
% 0.21/0.48         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.48           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X46 @ X47)
% 0.21/0.48          | ((X48) = (k1_xboole_0))
% 0.21/0.48          | ~ (v1_funct_1 @ X49)
% 0.21/0.48          | ~ (v1_funct_2 @ X49 @ X47 @ X48)
% 0.21/0.48          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 0.21/0.48          | (r2_hidden @ (k1_funct_1 @ X49 @ X46) @ X48))),
% 0.21/0.48      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ (k1_tarski @ sk_B))
% 0.21/0.48          | ~ (v1_funct_2 @ sk_D_1 @ sk_A @ (k1_tarski @ sk_B))
% 0.21/0.48          | ~ (v1_funct_1 @ sk_D_1)
% 0.21/0.48          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.21/0.48          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.48  thf('4', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ (k1_tarski @ sk_B))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('5', plain, ((v1_funct_1 @ sk_D_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ (k1_tarski @ sk_B))
% 0.21/0.48          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.21/0.48          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.21/0.48        | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_C_1) @ (k1_tarski @ sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '6'])).
% 0.21/0.48  thf(t20_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.48         ( k1_tarski @ A ) ) <=>
% 0.21/0.48       ( ( A ) != ( B ) ) ))).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X44 : $i, X45 : $i]:
% 0.21/0.48         (((k4_xboole_0 @ (k1_tarski @ X44) @ (k1_tarski @ X45))
% 0.21/0.48            = (k1_tarski @ X44))
% 0.21/0.48          | ((X44) = (X45)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.21/0.48  thf(l33_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.48       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X40 : $i, X41 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X40 @ X41)
% 0.21/0.48          | ((k4_xboole_0 @ (k1_tarski @ X40) @ X41) != (k1_tarski @ X40)))),
% 0.21/0.48      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.21/0.48          | ((X0) = (X1))
% 0.21/0.48          | ~ (r2_hidden @ X0 @ (k1_tarski @ X1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X0 @ (k1_tarski @ X1)) | ((X0) = (X1)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.21/0.48        | ((k1_funct_1 @ sk_D_1 @ sk_C_1) = (sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['7', '11'])).
% 0.21/0.48  thf('13', plain, (((k1_funct_1 @ sk_D_1 @ sk_C_1) != (sk_B))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('14', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (![X43 : $i, X44 : $i]:
% 0.21/0.48         (((X44) != (X43))
% 0.21/0.48          | ((k4_xboole_0 @ (k1_tarski @ X44) @ (k1_tarski @ X43))
% 0.21/0.48              != (k1_tarski @ X44)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      (![X43 : $i]:
% 0.21/0.48         ((k4_xboole_0 @ (k1_tarski @ X43) @ (k1_tarski @ X43))
% 0.21/0.48           != (k1_tarski @ X43))),
% 0.21/0.48      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0) != (k1_tarski @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['14', '16'])).
% 0.21/0.48  thf('18', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.21/0.48  thf(t3_boole, axiom,
% 0.21/0.48    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.48  thf('19', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.48  thf('20', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.21/0.48  thf('21', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.48      inference('demod', [status(thm)], ['17', '18', '19', '20'])).
% 0.21/0.48  thf('22', plain, ($false), inference('simplify', [status(thm)], ['21'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
