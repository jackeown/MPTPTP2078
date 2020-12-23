%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Lj8ntJ107l

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   42 (  54 expanded)
%              Number of leaves         :   19 (  25 expanded)
%              Depth                    :   12
%              Number of atoms          :  243 ( 483 expanded)
%              Number of equality atoms :   20 (  34 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ( k1_funct_1 @ sk_D @ sk_C_1 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ( X11 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_2 @ X12 @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X12 @ X9 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('9',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( X4 = X1 )
      | ( X3
       != ( k1_tarski @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('10',plain,(
    ! [X1: $i,X4: $i] :
      ( ( X4 = X1 )
      | ~ ( r2_hidden @ X4 @ ( k1_tarski @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_funct_1 @ sk_D @ sk_C_1 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ( k1_funct_1 @ sk_D @ sk_C_1 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('14',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_tarski @ ( k1_tarski @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_B @ X0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X1: $i,X4: $i] :
      ( ( X4 = X1 )
      | ~ ( r2_hidden @ X4 @ ( k1_tarski @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('19',plain,(
    ! [X0: $i] : ( sk_B = X0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    sk_B != sk_B ),
    inference(demod,[status(thm)],['0','19'])).

thf('21',plain,(
    $false ),
    inference(simplify,[status(thm)],['20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Lj8ntJ107l
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:58:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 26 iterations in 0.012s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.47  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.47  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.47  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.47  thf(t65_funct_2, conjecture,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.47     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.20/0.47         ( m1_subset_1 @
% 0.20/0.47           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.20/0.47       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.47        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.20/0.47            ( m1_subset_1 @
% 0.20/0.47              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.20/0.47          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.20/0.47  thf('0', plain, (((k1_funct_1 @ sk_D @ sk_C_1) != (sk_B))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('1', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_D @ 
% 0.20/0.47        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t7_funct_2, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.47     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.47         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.47       ( ( r2_hidden @ C @ A ) =>
% 0.20/0.47         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.47           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X9 @ X10)
% 0.20/0.47          | ((X11) = (k1_xboole_0))
% 0.20/0.47          | ~ (v1_funct_1 @ X12)
% 0.20/0.47          | ~ (v1_funct_2 @ X12 @ X10 @ X11)
% 0.20/0.47          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 0.20/0.47          | (r2_hidden @ (k1_funct_1 @ X12 @ X9) @ X11))),
% 0.20/0.47      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.20/0.47          | ~ (v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))
% 0.20/0.47          | ~ (v1_funct_1 @ sk_D)
% 0.20/0.47          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.20/0.47          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.47  thf('5', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('6', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.20/0.47          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.20/0.47          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.20/0.47        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C_1) @ (k1_tarski @ sk_B)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '7'])).
% 0.20/0.47  thf(d1_tarski, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X4 @ X3) | ((X4) = (X1)) | ((X3) != (k1_tarski @ X1)))),
% 0.20/0.47      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X1 : $i, X4 : $i]:
% 0.20/0.47         (((X4) = (X1)) | ~ (r2_hidden @ X4 @ (k1_tarski @ X1)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['9'])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.20/0.47        | ((k1_funct_1 @ sk_D @ sk_C_1) = (sk_B)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['8', '10'])).
% 0.20/0.47  thf('12', plain, (((k1_funct_1 @ sk_D @ sk_C_1) != (sk_B))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('13', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.20/0.47  thf(l1_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X6 : $i, X7 : $i]:
% 0.20/0.47         ((r2_hidden @ X6 @ X7) | ~ (r1_tarski @ (k1_tarski @ X6) @ X7))),
% 0.20/0.47      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X0 : $i]: (~ (r1_tarski @ k1_xboole_0 @ X0) | (r2_hidden @ sk_B @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.47  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.47  thf('16', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.47      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.47  thf('17', plain, (![X0 : $i]: (r2_hidden @ sk_B @ X0)),
% 0.20/0.47      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      (![X1 : $i, X4 : $i]:
% 0.20/0.47         (((X4) = (X1)) | ~ (r2_hidden @ X4 @ (k1_tarski @ X1)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['9'])).
% 0.20/0.47  thf('19', plain, (![X0 : $i]: ((sk_B) = (X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.47  thf('20', plain, (((sk_B) != (sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['0', '19'])).
% 0.20/0.47  thf('21', plain, ($false), inference('simplify', [status(thm)], ['20'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
