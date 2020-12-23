%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iBGL2SX6SW

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:44 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :   50 (  72 expanded)
%              Number of leaves         :   21 (  31 expanded)
%              Depth                    :   12
%              Number of atoms          :  282 ( 474 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t68_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( v1_xboole_0 @ C )
     => ~ ( ( r1_tarski @ C @ A )
          & ( r1_tarski @ C @ B )
          & ( r1_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ~ ( v1_xboole_0 @ C )
       => ~ ( ( r1_tarski @ C @ A )
            & ( r1_tarski @ C @ B )
            & ( r1_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t68_xboole_1])).

thf('0',plain,(
    r1_xboole_0 @ sk_A @ sk_B_1 ),
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
    r1_tarski @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( r2_hidden @ ( sk_B @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r2_hidden @ ( sk_B @ sk_C_1 ) @ sk_B_1 ),
    inference(clc,[status(thm)],['5','6'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( r2_hidden @ X7 @ X9 )
      | ( X9
       != ( k2_xboole_0 @ X10 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('9',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X7 @ ( k2_xboole_0 @ X10 @ X8 ) )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_B @ sk_C_1 ) @ ( k2_xboole_0 @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

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

thf('11',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_xboole_0 @ X19 @ X20 )
      | ( zip_tseitin_0 @ X21 @ X20 @ X19 )
      | ( zip_tseitin_1 @ X21 @ X20 @ X19 )
      | ~ ( r2_hidden @ X21 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ ( sk_B @ sk_C_1 ) @ sk_B_1 @ X0 )
      | ( zip_tseitin_0 @ ( sk_B @ sk_C_1 ) @ sk_B_1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( zip_tseitin_0 @ ( sk_B @ sk_C_1 ) @ sk_B_1 @ sk_A )
    | ( zip_tseitin_1 @ ( sk_B @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','12'])).

thf('14',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ X18 )
      | ~ ( zip_tseitin_1 @ X16 @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('15',plain,
    ( ( zip_tseitin_0 @ ( sk_B @ sk_C_1 ) @ sk_B_1 @ sk_A )
    | ~ ( r2_hidden @ ( sk_B @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r2_hidden @ ( sk_B @ sk_C_1 ) @ sk_B_1 ),
    inference(clc,[status(thm)],['5','6'])).

thf('17',plain,(
    zip_tseitin_0 @ ( sk_B @ sk_C_1 ) @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X15 )
      | ~ ( zip_tseitin_0 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('19',plain,(
    ~ ( r2_hidden @ ( sk_B @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('21',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( r2_hidden @ ( sk_B @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    r2_hidden @ ( sk_B @ sk_C_1 ) @ sk_A ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['19','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iBGL2SX6SW
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:12:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.28/1.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.28/1.48  % Solved by: fo/fo7.sh
% 1.28/1.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.28/1.48  % done 1549 iterations in 1.029s
% 1.28/1.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.28/1.48  % SZS output start Refutation
% 1.28/1.48  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.28/1.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.28/1.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.28/1.48  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 1.28/1.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.28/1.48  thf(sk_B_type, type, sk_B: $i > $i).
% 1.28/1.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.28/1.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.28/1.48  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.28/1.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.28/1.48  thf(sk_A_type, type, sk_A: $i).
% 1.28/1.48  thf(t68_xboole_1, conjecture,
% 1.28/1.48    (![A:$i,B:$i,C:$i]:
% 1.28/1.48     ( ( ~( v1_xboole_0 @ C ) ) =>
% 1.28/1.48       ( ~( ( r1_tarski @ C @ A ) & ( r1_tarski @ C @ B ) & 
% 1.28/1.48            ( r1_xboole_0 @ A @ B ) ) ) ))).
% 1.28/1.48  thf(zf_stmt_0, negated_conjecture,
% 1.28/1.48    (~( ![A:$i,B:$i,C:$i]:
% 1.28/1.48        ( ( ~( v1_xboole_0 @ C ) ) =>
% 1.28/1.48          ( ~( ( r1_tarski @ C @ A ) & ( r1_tarski @ C @ B ) & 
% 1.28/1.48               ( r1_xboole_0 @ A @ B ) ) ) ) )),
% 1.28/1.48    inference('cnf.neg', [status(esa)], [t68_xboole_1])).
% 1.28/1.48  thf('0', plain, ((r1_xboole_0 @ sk_A @ sk_B_1)),
% 1.28/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.48  thf(d1_xboole_0, axiom,
% 1.28/1.48    (![A:$i]:
% 1.28/1.48     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.28/1.48  thf('1', plain,
% 1.28/1.48      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.28/1.48      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.28/1.48  thf('2', plain, ((r1_tarski @ sk_C_1 @ sk_B_1)),
% 1.28/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.48  thf(d3_tarski, axiom,
% 1.28/1.48    (![A:$i,B:$i]:
% 1.28/1.48     ( ( r1_tarski @ A @ B ) <=>
% 1.28/1.48       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.28/1.48  thf('3', plain,
% 1.28/1.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.28/1.48         (~ (r2_hidden @ X3 @ X4)
% 1.28/1.48          | (r2_hidden @ X3 @ X5)
% 1.28/1.48          | ~ (r1_tarski @ X4 @ X5))),
% 1.28/1.48      inference('cnf', [status(esa)], [d3_tarski])).
% 1.28/1.48  thf('4', plain,
% 1.28/1.48      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B_1) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 1.28/1.48      inference('sup-', [status(thm)], ['2', '3'])).
% 1.28/1.48  thf('5', plain,
% 1.28/1.48      (((v1_xboole_0 @ sk_C_1) | (r2_hidden @ (sk_B @ sk_C_1) @ sk_B_1))),
% 1.28/1.48      inference('sup-', [status(thm)], ['1', '4'])).
% 1.28/1.48  thf('6', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 1.28/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.48  thf('7', plain, ((r2_hidden @ (sk_B @ sk_C_1) @ sk_B_1)),
% 1.28/1.48      inference('clc', [status(thm)], ['5', '6'])).
% 1.28/1.48  thf(d3_xboole_0, axiom,
% 1.28/1.48    (![A:$i,B:$i,C:$i]:
% 1.28/1.48     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 1.28/1.48       ( ![D:$i]:
% 1.28/1.48         ( ( r2_hidden @ D @ C ) <=>
% 1.28/1.48           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.28/1.48  thf('8', plain,
% 1.28/1.48      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.28/1.48         (~ (r2_hidden @ X7 @ X8)
% 1.28/1.48          | (r2_hidden @ X7 @ X9)
% 1.28/1.48          | ((X9) != (k2_xboole_0 @ X10 @ X8)))),
% 1.28/1.48      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.28/1.48  thf('9', plain,
% 1.28/1.48      (![X7 : $i, X8 : $i, X10 : $i]:
% 1.28/1.48         ((r2_hidden @ X7 @ (k2_xboole_0 @ X10 @ X8)) | ~ (r2_hidden @ X7 @ X8))),
% 1.28/1.48      inference('simplify', [status(thm)], ['8'])).
% 1.28/1.48  thf('10', plain,
% 1.28/1.48      (![X0 : $i]: (r2_hidden @ (sk_B @ sk_C_1) @ (k2_xboole_0 @ X0 @ sk_B_1))),
% 1.28/1.48      inference('sup-', [status(thm)], ['7', '9'])).
% 1.28/1.48  thf(t5_xboole_0, axiom,
% 1.28/1.48    (![A:$i,B:$i,C:$i]:
% 1.28/1.48     ( ~( ( ~( ( ~( r2_hidden @ C @ A ) ) & ( r2_hidden @ C @ B ) ) ) & 
% 1.28/1.48          ( ~( ( ~( r2_hidden @ C @ B ) ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.28/1.48          ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) ) & ( r1_xboole_0 @ A @ B ) ) ))).
% 1.28/1.48  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.28/1.48  thf(zf_stmt_2, axiom,
% 1.28/1.48    (![C:$i,B:$i,A:$i]:
% 1.28/1.48     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.28/1.48       ( ( r2_hidden @ C @ A ) & ( ~( r2_hidden @ C @ B ) ) ) ))).
% 1.28/1.48  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $i > $o).
% 1.28/1.48  thf(zf_stmt_4, axiom,
% 1.28/1.48    (![C:$i,B:$i,A:$i]:
% 1.28/1.48     ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 1.28/1.48       ( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ))).
% 1.28/1.48  thf(zf_stmt_5, axiom,
% 1.28/1.48    (![A:$i,B:$i,C:$i]:
% 1.28/1.48     ( ~( ( r1_xboole_0 @ A @ B ) & 
% 1.28/1.48          ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) ) & 
% 1.28/1.48          ( ~( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.28/1.48          ( ~( zip_tseitin_0 @ C @ B @ A ) ) ) ))).
% 1.28/1.48  thf('11', plain,
% 1.28/1.48      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.28/1.48         (~ (r1_xboole_0 @ X19 @ X20)
% 1.28/1.48          | (zip_tseitin_0 @ X21 @ X20 @ X19)
% 1.28/1.48          | (zip_tseitin_1 @ X21 @ X20 @ X19)
% 1.28/1.48          | ~ (r2_hidden @ X21 @ (k2_xboole_0 @ X19 @ X20)))),
% 1.28/1.48      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.28/1.48  thf('12', plain,
% 1.28/1.48      (![X0 : $i]:
% 1.28/1.48         ((zip_tseitin_1 @ (sk_B @ sk_C_1) @ sk_B_1 @ X0)
% 1.28/1.48          | (zip_tseitin_0 @ (sk_B @ sk_C_1) @ sk_B_1 @ X0)
% 1.28/1.48          | ~ (r1_xboole_0 @ X0 @ sk_B_1))),
% 1.28/1.48      inference('sup-', [status(thm)], ['10', '11'])).
% 1.28/1.48  thf('13', plain,
% 1.28/1.48      (((zip_tseitin_0 @ (sk_B @ sk_C_1) @ sk_B_1 @ sk_A)
% 1.28/1.48        | (zip_tseitin_1 @ (sk_B @ sk_C_1) @ sk_B_1 @ sk_A))),
% 1.28/1.48      inference('sup-', [status(thm)], ['0', '12'])).
% 1.28/1.48  thf('14', plain,
% 1.28/1.48      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.28/1.48         (~ (r2_hidden @ X16 @ X18) | ~ (zip_tseitin_1 @ X16 @ X18 @ X17))),
% 1.28/1.48      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.28/1.48  thf('15', plain,
% 1.28/1.48      (((zip_tseitin_0 @ (sk_B @ sk_C_1) @ sk_B_1 @ sk_A)
% 1.28/1.48        | ~ (r2_hidden @ (sk_B @ sk_C_1) @ sk_B_1))),
% 1.28/1.48      inference('sup-', [status(thm)], ['13', '14'])).
% 1.28/1.48  thf('16', plain, ((r2_hidden @ (sk_B @ sk_C_1) @ sk_B_1)),
% 1.28/1.48      inference('clc', [status(thm)], ['5', '6'])).
% 1.28/1.48  thf('17', plain, ((zip_tseitin_0 @ (sk_B @ sk_C_1) @ sk_B_1 @ sk_A)),
% 1.28/1.48      inference('demod', [status(thm)], ['15', '16'])).
% 1.28/1.48  thf('18', plain,
% 1.28/1.48      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.28/1.48         (~ (r2_hidden @ X13 @ X15) | ~ (zip_tseitin_0 @ X13 @ X14 @ X15))),
% 1.28/1.48      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.28/1.48  thf('19', plain, (~ (r2_hidden @ (sk_B @ sk_C_1) @ sk_A)),
% 1.28/1.48      inference('sup-', [status(thm)], ['17', '18'])).
% 1.28/1.48  thf('20', plain,
% 1.28/1.48      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.28/1.48      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.28/1.48  thf('21', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 1.28/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.48  thf('22', plain,
% 1.28/1.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.28/1.48         (~ (r2_hidden @ X3 @ X4)
% 1.28/1.48          | (r2_hidden @ X3 @ X5)
% 1.28/1.48          | ~ (r1_tarski @ X4 @ X5))),
% 1.28/1.48      inference('cnf', [status(esa)], [d3_tarski])).
% 1.28/1.48  thf('23', plain,
% 1.28/1.48      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 1.28/1.48      inference('sup-', [status(thm)], ['21', '22'])).
% 1.28/1.48  thf('24', plain,
% 1.28/1.48      (((v1_xboole_0 @ sk_C_1) | (r2_hidden @ (sk_B @ sk_C_1) @ sk_A))),
% 1.28/1.48      inference('sup-', [status(thm)], ['20', '23'])).
% 1.28/1.48  thf('25', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 1.28/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.48  thf('26', plain, ((r2_hidden @ (sk_B @ sk_C_1) @ sk_A)),
% 1.28/1.48      inference('clc', [status(thm)], ['24', '25'])).
% 1.28/1.48  thf('27', plain, ($false), inference('demod', [status(thm)], ['19', '26'])).
% 1.28/1.48  
% 1.28/1.48  % SZS output end Refutation
% 1.28/1.48  
% 1.35/1.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
