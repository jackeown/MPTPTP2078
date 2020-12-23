%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uG3Bu34bXj

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:29 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   43 (  51 expanded)
%              Number of leaves         :   21 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :  254 ( 430 expanded)
%              Number of equality atoms :   25 (  33 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ( X24 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X25 @ X22 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('8',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( X8 = X5 )
      | ( X7
       != ( k1_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('9',plain,(
    ! [X5: $i,X8: $i] :
      ( ( X8 = X5 )
      | ~ ( r2_hidden @ X8 @ ( k1_tarski @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_funct_1 @ sk_D @ sk_C_1 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ( k1_funct_1 @ sk_D @ sk_C_1 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('17',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X20 ) @ X21 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,(
    $false ),
    inference(simplify,[status(thm)],['19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uG3Bu34bXj
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:07:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.36  % Running in FO mode
% 0.22/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.47  % Solved by: fo/fo7.sh
% 0.22/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.47  % done 30 iterations in 0.017s
% 0.22/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.47  % SZS output start Refutation
% 0.22/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.47  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.47  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.47  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.47  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.47  thf(t65_funct_2, conjecture,
% 0.22/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.47     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.22/0.47         ( m1_subset_1 @
% 0.22/0.47           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.22/0.47       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.22/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.47    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.47        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.22/0.47            ( m1_subset_1 @
% 0.22/0.47              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.22/0.47          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.22/0.47    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.22/0.47  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('1', plain,
% 0.22/0.47      ((m1_subset_1 @ sk_D @ 
% 0.22/0.47        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf(t7_funct_2, axiom,
% 0.22/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.47     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.22/0.47         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.47       ( ( r2_hidden @ C @ A ) =>
% 0.22/0.47         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.22/0.47           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.22/0.47  thf('2', plain,
% 0.22/0.47      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.22/0.47         (~ (r2_hidden @ X22 @ X23)
% 0.22/0.47          | ((X24) = (k1_xboole_0))
% 0.22/0.47          | ~ (v1_funct_1 @ X25)
% 0.22/0.47          | ~ (v1_funct_2 @ X25 @ X23 @ X24)
% 0.22/0.47          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.22/0.47          | (r2_hidden @ (k1_funct_1 @ X25 @ X22) @ X24))),
% 0.22/0.47      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.22/0.47  thf('3', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.22/0.47          | ~ (v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))
% 0.22/0.47          | ~ (v1_funct_1 @ sk_D)
% 0.22/0.47          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.22/0.47          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.22/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.47  thf('4', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('5', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('6', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.22/0.47          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.22/0.47          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.22/0.47      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.22/0.47  thf('7', plain,
% 0.22/0.47      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.22/0.47        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C_1) @ (k1_tarski @ sk_B)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['0', '6'])).
% 0.22/0.47  thf(d1_tarski, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.22/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.22/0.47  thf('8', plain,
% 0.22/0.47      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.22/0.47         (~ (r2_hidden @ X8 @ X7) | ((X8) = (X5)) | ((X7) != (k1_tarski @ X5)))),
% 0.22/0.47      inference('cnf', [status(esa)], [d1_tarski])).
% 0.22/0.47  thf('9', plain,
% 0.22/0.47      (![X5 : $i, X8 : $i]:
% 0.22/0.47         (((X8) = (X5)) | ~ (r2_hidden @ X8 @ (k1_tarski @ X5)))),
% 0.22/0.47      inference('simplify', [status(thm)], ['8'])).
% 0.22/0.47  thf('10', plain,
% 0.22/0.47      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.22/0.47        | ((k1_funct_1 @ sk_D @ sk_C_1) = (sk_B)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['7', '9'])).
% 0.22/0.47  thf('11', plain, (((k1_funct_1 @ sk_D @ sk_C_1) != (sk_B))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('12', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.22/0.47      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.22/0.47  thf(d10_xboole_0, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.47  thf('13', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.22/0.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.47  thf('14', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.47      inference('simplify', [status(thm)], ['13'])).
% 0.22/0.47  thf(t12_xboole_1, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.22/0.47  thf('15', plain,
% 0.22/0.47      (![X3 : $i, X4 : $i]:
% 0.22/0.47         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.22/0.47      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.22/0.47  thf('16', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.22/0.47      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.47  thf(t49_zfmisc_1, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.22/0.47  thf('17', plain,
% 0.22/0.47      (![X20 : $i, X21 : $i]:
% 0.22/0.47         ((k2_xboole_0 @ (k1_tarski @ X20) @ X21) != (k1_xboole_0))),
% 0.22/0.47      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.22/0.47  thf('18', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.22/0.47      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.47  thf('19', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.47      inference('sup-', [status(thm)], ['12', '18'])).
% 0.22/0.47  thf('20', plain, ($false), inference('simplify', [status(thm)], ['19'])).
% 0.22/0.47  
% 0.22/0.47  % SZS output end Refutation
% 0.22/0.47  
% 0.22/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
