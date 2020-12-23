%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.COkItIuYGX

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:47 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   47 (  57 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :  270 ( 344 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t69_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ~ ( v1_xboole_0 @ B )
       => ~ ( ( r1_tarski @ B @ A )
            & ( r1_xboole_0 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t69_xboole_1])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('2',plain,(
    r1_xboole_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X7 @ X10 )
      | ( r2_hidden @ X7 @ X9 )
      | ( X9
       != ( k2_xboole_0 @ X10 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('5',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X7 @ ( k2_xboole_0 @ X10 @ X8 ) )
      | ~ ( r2_hidden @ X7 @ X10 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf(t5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( ~ ( r2_hidden @ C @ A )
            & ( r2_hidden @ C @ B ) )
        & ~ ( ~ ( r2_hidden @ C @ B )
            & ( r2_hidden @ C @ A ) )
        & ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) )
        & ( r1_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( r2_hidden @ C @ A )
        & ~ ( r2_hidden @ C @ B ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ C @ B @ A )
     => ( ( r2_hidden @ C @ B )
        & ~ ( r2_hidden @ C @ A ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ A @ B )
        & ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) )
        & ~ ( zip_tseitin_1 @ C @ B @ A )
        & ~ ( zip_tseitin_0 @ C @ B @ A ) ) )).

thf('7',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_xboole_0 @ X19 @ X20 )
      | ( zip_tseitin_0 @ X21 @ X20 @ X19 )
      | ( zip_tseitin_1 @ X21 @ X20 @ X19 )
      | ~ ( r2_hidden @ X21 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ( zip_tseitin_1 @ ( sk_B @ X1 ) @ X0 @ X1 )
      | ( zip_tseitin_0 @ ( sk_B @ X1 ) @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( zip_tseitin_0 @ ( sk_B @ sk_B_1 ) @ sk_A @ sk_B_1 )
    | ( zip_tseitin_1 @ ( sk_B @ sk_B_1 ) @ sk_A @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( zip_tseitin_1 @ ( sk_B @ sk_B_1 ) @ sk_A @ sk_B_1 )
    | ( zip_tseitin_0 @ ( sk_B @ sk_B_1 ) @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ X18 )
      | ~ ( zip_tseitin_1 @ X16 @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('13',plain,
    ( ( zip_tseitin_0 @ ( sk_B @ sk_B_1 ) @ sk_A @ sk_B_1 )
    | ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('15',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    zip_tseitin_0 @ ( sk_B @ sk_B_1 ) @ sk_A @ sk_B_1 ),
    inference(demod,[status(thm)],['13','20'])).

thf('22',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X15 )
      | ~ ( zip_tseitin_0 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('23',plain,(
    ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['1','23'])).

thf('25',plain,(
    $false ),
    inference(demod,[status(thm)],['0','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.COkItIuYGX
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:05:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.40/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.58  % Solved by: fo/fo7.sh
% 0.40/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.58  % done 159 iterations in 0.141s
% 0.40/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.58  % SZS output start Refutation
% 0.40/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.58  thf(sk_B_type, type, sk_B: $i > $i).
% 0.40/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.58  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.40/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.40/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.40/0.58  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.40/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.40/0.58  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.40/0.58  thf(t69_xboole_1, conjecture,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.40/0.58       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.40/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.58    (~( ![A:$i,B:$i]:
% 0.40/0.58        ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.40/0.58          ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) )),
% 0.40/0.58    inference('cnf.neg', [status(esa)], [t69_xboole_1])).
% 0.40/0.58  thf('0', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(d1_xboole_0, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.40/0.58  thf('1', plain,
% 0.40/0.58      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.40/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.40/0.58  thf('2', plain, ((r1_xboole_0 @ sk_B_1 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('3', plain,
% 0.40/0.58      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.40/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.40/0.58  thf(d3_xboole_0, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.40/0.58       ( ![D:$i]:
% 0.40/0.58         ( ( r2_hidden @ D @ C ) <=>
% 0.40/0.58           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.40/0.58  thf('4', plain,
% 0.40/0.58      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.40/0.58         (~ (r2_hidden @ X7 @ X10)
% 0.40/0.58          | (r2_hidden @ X7 @ X9)
% 0.40/0.58          | ((X9) != (k2_xboole_0 @ X10 @ X8)))),
% 0.40/0.58      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.40/0.58  thf('5', plain,
% 0.40/0.58      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.40/0.58         ((r2_hidden @ X7 @ (k2_xboole_0 @ X10 @ X8))
% 0.40/0.58          | ~ (r2_hidden @ X7 @ X10))),
% 0.40/0.58      inference('simplify', [status(thm)], ['4'])).
% 0.40/0.58  thf('6', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((v1_xboole_0 @ X0)
% 0.40/0.58          | (r2_hidden @ (sk_B @ X0) @ (k2_xboole_0 @ X0 @ X1)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['3', '5'])).
% 0.40/0.58  thf(t5_xboole_0, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ~( ( ~( ( ~( r2_hidden @ C @ A ) ) & ( r2_hidden @ C @ B ) ) ) & 
% 0.40/0.58          ( ~( ( ~( r2_hidden @ C @ B ) ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.40/0.58          ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) ) & ( r1_xboole_0 @ A @ B ) ) ))).
% 0.40/0.58  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.40/0.58  thf(zf_stmt_2, axiom,
% 0.40/0.58    (![C:$i,B:$i,A:$i]:
% 0.40/0.58     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.40/0.58       ( ( r2_hidden @ C @ A ) & ( ~( r2_hidden @ C @ B ) ) ) ))).
% 0.40/0.58  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.40/0.58  thf(zf_stmt_4, axiom,
% 0.40/0.58    (![C:$i,B:$i,A:$i]:
% 0.40/0.58     ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.40/0.58       ( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ))).
% 0.40/0.58  thf(zf_stmt_5, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ~( ( r1_xboole_0 @ A @ B ) & 
% 0.40/0.58          ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) ) & 
% 0.40/0.58          ( ~( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.40/0.58          ( ~( zip_tseitin_0 @ C @ B @ A ) ) ) ))).
% 0.40/0.58  thf('7', plain,
% 0.40/0.58      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.40/0.58         (~ (r1_xboole_0 @ X19 @ X20)
% 0.40/0.58          | (zip_tseitin_0 @ X21 @ X20 @ X19)
% 0.40/0.58          | (zip_tseitin_1 @ X21 @ X20 @ X19)
% 0.40/0.58          | ~ (r2_hidden @ X21 @ (k2_xboole_0 @ X19 @ X20)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.40/0.58  thf('8', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((v1_xboole_0 @ X1)
% 0.40/0.58          | (zip_tseitin_1 @ (sk_B @ X1) @ X0 @ X1)
% 0.40/0.58          | (zip_tseitin_0 @ (sk_B @ X1) @ X0 @ X1)
% 0.40/0.58          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['6', '7'])).
% 0.40/0.58  thf('9', plain,
% 0.40/0.58      (((zip_tseitin_0 @ (sk_B @ sk_B_1) @ sk_A @ sk_B_1)
% 0.40/0.58        | (zip_tseitin_1 @ (sk_B @ sk_B_1) @ sk_A @ sk_B_1)
% 0.40/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.40/0.58      inference('sup-', [status(thm)], ['2', '8'])).
% 0.40/0.58  thf('10', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('11', plain,
% 0.40/0.58      (((zip_tseitin_1 @ (sk_B @ sk_B_1) @ sk_A @ sk_B_1)
% 0.40/0.58        | (zip_tseitin_0 @ (sk_B @ sk_B_1) @ sk_A @ sk_B_1))),
% 0.40/0.58      inference('clc', [status(thm)], ['9', '10'])).
% 0.40/0.58  thf('12', plain,
% 0.40/0.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.40/0.58         (~ (r2_hidden @ X16 @ X18) | ~ (zip_tseitin_1 @ X16 @ X18 @ X17))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.40/0.58  thf('13', plain,
% 0.40/0.58      (((zip_tseitin_0 @ (sk_B @ sk_B_1) @ sk_A @ sk_B_1)
% 0.40/0.58        | ~ (r2_hidden @ (sk_B @ sk_B_1) @ sk_A))),
% 0.40/0.58      inference('sup-', [status(thm)], ['11', '12'])).
% 0.40/0.58  thf('14', plain,
% 0.40/0.58      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.40/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.40/0.58  thf('15', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(d3_tarski, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( r1_tarski @ A @ B ) <=>
% 0.40/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.40/0.58  thf('16', plain,
% 0.40/0.58      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.40/0.58         (~ (r2_hidden @ X3 @ X4)
% 0.40/0.58          | (r2_hidden @ X3 @ X5)
% 0.40/0.58          | ~ (r1_tarski @ X4 @ X5))),
% 0.40/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.58  thf('17', plain,
% 0.40/0.58      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.40/0.58      inference('sup-', [status(thm)], ['15', '16'])).
% 0.40/0.58  thf('18', plain,
% 0.40/0.58      (((v1_xboole_0 @ sk_B_1) | (r2_hidden @ (sk_B @ sk_B_1) @ sk_A))),
% 0.40/0.58      inference('sup-', [status(thm)], ['14', '17'])).
% 0.40/0.58  thf('19', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('20', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ sk_A)),
% 0.40/0.58      inference('clc', [status(thm)], ['18', '19'])).
% 0.40/0.58  thf('21', plain, ((zip_tseitin_0 @ (sk_B @ sk_B_1) @ sk_A @ sk_B_1)),
% 0.40/0.58      inference('demod', [status(thm)], ['13', '20'])).
% 0.40/0.58  thf('22', plain,
% 0.40/0.58      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.40/0.58         (~ (r2_hidden @ X13 @ X15) | ~ (zip_tseitin_0 @ X13 @ X14 @ X15))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.40/0.58  thf('23', plain, (~ (r2_hidden @ (sk_B @ sk_B_1) @ sk_B_1)),
% 0.40/0.58      inference('sup-', [status(thm)], ['21', '22'])).
% 0.40/0.58  thf('24', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.40/0.58      inference('sup-', [status(thm)], ['1', '23'])).
% 0.40/0.58  thf('25', plain, ($false), inference('demod', [status(thm)], ['0', '24'])).
% 0.40/0.58  
% 0.40/0.58  % SZS output end Refutation
% 0.40/0.58  
% 0.40/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
