%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mD46zJlYZL

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:32 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 150 expanded)
%              Number of leaves         :   18 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :  278 (1797 expanded)
%              Number of equality atoms :   37 ( 164 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ( k1_funct_1 @ sk_D @ sk_C_2 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_C_2 @ sk_A ),
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
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ( X21 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_2 @ X22 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X22 @ X19 ) @ X21 ) ) ),
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
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C_2 ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('9',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( X7 = X4 )
      | ( X6
       != ( k1_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('10',plain,(
    ! [X4: $i,X7: $i] :
      ( ( X7 = X4 )
      | ~ ( r2_hidden @ X7 @ ( k1_tarski @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_funct_1 @ sk_D @ sk_C_2 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ( k1_funct_1 @ sk_D @ sk_C_2 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf(t130_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != k1_xboole_0 )
     => ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A )
         != k1_xboole_0 )
        & ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) )
         != k1_xboole_0 ) ) ) )).

thf('14',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ ( k1_tarski @ X16 ) @ X15 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t130_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_zfmisc_1 @ X13 @ X14 )
        = k1_xboole_0 )
      | ( X13 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('17',plain,(
    ! [X14: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X14 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('21',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('22',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('23',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','19','20','21','22'])).

thf('24',plain,(
    $false ),
    inference(simplify,[status(thm)],['23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mD46zJlYZL
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:34:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 44 iterations in 0.027s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.48  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.22/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.48  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.48  thf(t65_funct_2, conjecture,
% 0.22/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.48     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.22/0.48         ( m1_subset_1 @
% 0.22/0.48           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.22/0.48       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.48        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.22/0.48            ( m1_subset_1 @
% 0.22/0.48              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.22/0.48          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.22/0.48  thf('0', plain, (((k1_funct_1 @ sk_D @ sk_C_2) != (sk_B))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('1', plain, ((r2_hidden @ sk_C_2 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('2', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_D @ 
% 0.22/0.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(t7_funct_2, axiom,
% 0.22/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.48     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.22/0.48         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.48       ( ( r2_hidden @ C @ A ) =>
% 0.22/0.48         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.22/0.48           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.22/0.48  thf('3', plain,
% 0.22/0.48      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.48         (~ (r2_hidden @ X19 @ X20)
% 0.22/0.48          | ((X21) = (k1_xboole_0))
% 0.22/0.48          | ~ (v1_funct_1 @ X22)
% 0.22/0.48          | ~ (v1_funct_2 @ X22 @ X20 @ X21)
% 0.22/0.48          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.22/0.48          | (r2_hidden @ (k1_funct_1 @ X22 @ X19) @ X21))),
% 0.22/0.48      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.22/0.48  thf('4', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.22/0.48          | ~ (v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))
% 0.22/0.48          | ~ (v1_funct_1 @ sk_D)
% 0.22/0.48          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.22/0.48          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.48  thf('5', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('6', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('7', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.22/0.48          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.22/0.48          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.22/0.48      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.22/0.48  thf('8', plain,
% 0.22/0.48      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.22/0.48        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C_2) @ (k1_tarski @ sk_B)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['1', '7'])).
% 0.22/0.48  thf(d1_tarski, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.22/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.22/0.48  thf('9', plain,
% 0.22/0.48      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.22/0.48         (~ (r2_hidden @ X7 @ X6) | ((X7) = (X4)) | ((X6) != (k1_tarski @ X4)))),
% 0.22/0.48      inference('cnf', [status(esa)], [d1_tarski])).
% 0.22/0.48  thf('10', plain,
% 0.22/0.48      (![X4 : $i, X7 : $i]:
% 0.22/0.48         (((X7) = (X4)) | ~ (r2_hidden @ X7 @ (k1_tarski @ X4)))),
% 0.22/0.48      inference('simplify', [status(thm)], ['9'])).
% 0.22/0.48  thf('11', plain,
% 0.22/0.48      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.22/0.48        | ((k1_funct_1 @ sk_D @ sk_C_2) = (sk_B)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['8', '10'])).
% 0.22/0.48  thf('12', plain, (((k1_funct_1 @ sk_D @ sk_C_2) != (sk_B))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('13', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.22/0.48      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.22/0.48  thf(t130_zfmisc_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.22/0.48       ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.48         ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.22/0.48  thf('14', plain,
% 0.22/0.48      (![X15 : $i, X16 : $i]:
% 0.22/0.48         (((X15) = (k1_xboole_0))
% 0.22/0.48          | ((k2_zfmisc_1 @ (k1_tarski @ X16) @ X15) != (k1_xboole_0)))),
% 0.22/0.48      inference('cnf', [status(esa)], [t130_zfmisc_1])).
% 0.22/0.48  thf('15', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (((k2_zfmisc_1 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 0.22/0.48          | ((X0) = (k1_xboole_0)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.48  thf(t113_zfmisc_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.48       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.48  thf('16', plain,
% 0.22/0.48      (![X13 : $i, X14 : $i]:
% 0.22/0.48         (((k2_zfmisc_1 @ X13 @ X14) = (k1_xboole_0))
% 0.22/0.48          | ((X13) != (k1_xboole_0)))),
% 0.22/0.48      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.22/0.48  thf('17', plain,
% 0.22/0.48      (![X14 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X14) = (k1_xboole_0))),
% 0.22/0.48      inference('simplify', [status(thm)], ['16'])).
% 0.22/0.48  thf('18', plain,
% 0.22/0.48      (![X0 : $i]: (((k1_xboole_0) != (k1_xboole_0)) | ((X0) = (k1_xboole_0)))),
% 0.22/0.48      inference('demod', [status(thm)], ['15', '17'])).
% 0.22/0.48  thf('19', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 0.22/0.48      inference('simplify', [status(thm)], ['18'])).
% 0.22/0.48  thf('20', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 0.22/0.48      inference('simplify', [status(thm)], ['18'])).
% 0.22/0.48  thf('21', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 0.22/0.48      inference('simplify', [status(thm)], ['18'])).
% 0.22/0.48  thf('22', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 0.22/0.48      inference('simplify', [status(thm)], ['18'])).
% 0.22/0.48  thf('23', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.48      inference('demod', [status(thm)], ['0', '19', '20', '21', '22'])).
% 0.22/0.48  thf('24', plain, ($false), inference('simplify', [status(thm)], ['23'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
