%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0qhQxELL4N

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   42 (  51 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :  265 ( 451 expanded)
%              Number of equality atoms :   22 (  32 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( r2_hidden @ X49 @ X50 )
      | ( X51 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_funct_2 @ X52 @ X50 @ X51 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X52 @ X49 ) @ X51 ) ) ),
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

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('8',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( X10 = X7 )
      | ( X9
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('9',plain,(
    ! [X7: $i,X10: $i] :
      ( ( X10 = X7 )
      | ~ ( r2_hidden @ X10 @ ( k1_tarski @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_funct_1 @ sk_D_1 @ sk_C_1 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ( k1_funct_1 @ sk_D_1 @ sk_C_1 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( X8 != X7 )
      | ( r2_hidden @ X8 @ X9 )
      | ( X9
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('14',plain,(
    ! [X7: $i] :
      ( r2_hidden @ X7 @ ( k1_tarski @ X7 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    r2_hidden @ sk_B @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['12','14'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('16',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('17',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('18',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['19'])).

thf('21',plain,(
    $false ),
    inference('sup-',[status(thm)],['15','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0qhQxELL4N
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:49:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 121 iterations in 0.059s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.50  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.50  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(t65_funct_2, conjecture,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.50     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.21/0.50         ( m1_subset_1 @
% 0.21/0.50           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.21/0.50       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.50        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.21/0.50            ( m1_subset_1 @
% 0.21/0.50              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.21/0.50          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.21/0.50  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_D_1 @ 
% 0.21/0.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t7_funct_2, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.50     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.50         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.50       ( ( r2_hidden @ C @ A ) =>
% 0.21/0.50         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.50           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X49 @ X50)
% 0.21/0.50          | ((X51) = (k1_xboole_0))
% 0.21/0.50          | ~ (v1_funct_1 @ X52)
% 0.21/0.50          | ~ (v1_funct_2 @ X52 @ X50 @ X51)
% 0.21/0.50          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 0.21/0.50          | (r2_hidden @ (k1_funct_1 @ X52 @ X49) @ X51))),
% 0.21/0.50      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ (k1_tarski @ sk_B))
% 0.21/0.50          | ~ (v1_funct_2 @ sk_D_1 @ sk_A @ (k1_tarski @ sk_B))
% 0.21/0.50          | ~ (v1_funct_1 @ sk_D_1)
% 0.21/0.50          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.21/0.50          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.50  thf('4', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ (k1_tarski @ sk_B))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('5', plain, ((v1_funct_1 @ sk_D_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ (k1_tarski @ sk_B))
% 0.21/0.50          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.21/0.50          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.21/0.50        | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_C_1) @ (k1_tarski @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['0', '6'])).
% 0.21/0.50  thf(d1_tarski, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X10 @ X9)
% 0.21/0.50          | ((X10) = (X7))
% 0.21/0.50          | ((X9) != (k1_tarski @ X7)))),
% 0.21/0.50      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (![X7 : $i, X10 : $i]:
% 0.21/0.50         (((X10) = (X7)) | ~ (r2_hidden @ X10 @ (k1_tarski @ X7)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.21/0.50        | ((k1_funct_1 @ sk_D_1 @ sk_C_1) = (sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['7', '9'])).
% 0.21/0.50  thf('11', plain, (((k1_funct_1 @ sk_D_1 @ sk_C_1) != (sk_B))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('12', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.50         (((X8) != (X7)) | (r2_hidden @ X8 @ X9) | ((X9) != (k1_tarski @ X7)))),
% 0.21/0.50      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.50  thf('14', plain, (![X7 : $i]: (r2_hidden @ X7 @ (k1_tarski @ X7))),
% 0.21/0.50      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.50  thf('15', plain, ((r2_hidden @ sk_B @ k1_xboole_0)),
% 0.21/0.50      inference('sup+', [status(thm)], ['12', '14'])).
% 0.21/0.50  thf(t3_boole, axiom,
% 0.21/0.50    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.50  thf('16', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.50  thf(d5_xboole_0, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.21/0.50       ( ![D:$i]:
% 0.21/0.50         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.50           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X4 @ X3)
% 0.21/0.50          | ~ (r2_hidden @ X4 @ X2)
% 0.21/0.50          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.21/0.50      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X4 @ X2)
% 0.21/0.50          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['16', '18'])).
% 0.21/0.50  thf('20', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.50      inference('condensation', [status(thm)], ['19'])).
% 0.21/0.50  thf('21', plain, ($false), inference('sup-', [status(thm)], ['15', '20'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
