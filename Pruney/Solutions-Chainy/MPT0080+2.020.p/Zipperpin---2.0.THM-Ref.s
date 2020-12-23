%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0dFd822GT7

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:06 EST 2020

% Result     : Theorem 2.92s
% Output     : Refutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :   52 (  61 expanded)
%              Number of leaves         :   20 (  27 expanded)
%              Depth                    :   13
%              Number of atoms          :  376 ( 470 expanded)
%              Number of equality atoms :    3 (   4 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t73_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ C ) )
       => ( r1_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t73_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X7 )
      | ( X8
       != ( k2_xboole_0 @ X9 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('7',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ ( k2_xboole_0 @ X9 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ~ ( r1_xboole_0 @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('11',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( r2_hidden @ X6 @ X8 )
      | ( X8
       != ( k2_xboole_0 @ X9 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('14',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ( r2_hidden @ X6 @ ( k2_xboole_0 @ X9 @ X7 ) )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

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

thf('16',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_xboole_0 @ X20 @ X21 )
      | ( zip_tseitin_0 @ X22 @ X21 @ X20 )
      | ( zip_tseitin_1 @ X22 @ X21 @ X20 )
      | ~ ( r2_hidden @ X22 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X2 )
      | ( zip_tseitin_1 @ ( sk_C @ X2 @ X0 ) @ X0 @ X1 )
      | ( zip_tseitin_0 @ ( sk_C @ X2 @ X0 ) @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_C @ X0 @ sk_A ) @ sk_A @ sk_C_1 )
      | ( zip_tseitin_1 @ ( sk_C @ X0 @ sk_A ) @ sk_A @ sk_C_1 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X17 @ X19 )
      | ~ ( zip_tseitin_1 @ X17 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( zip_tseitin_0 @ ( sk_C @ X0 @ sk_A ) @ sk_A @ sk_C_1 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_C @ X0 @ sk_A ) @ sk_A @ sk_C_1 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X16 )
      | ~ ( zip_tseitin_0 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B )
      | ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['0','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0dFd822GT7
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:33:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.92/3.19  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.92/3.19  % Solved by: fo/fo7.sh
% 2.92/3.19  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.92/3.19  % done 2817 iterations in 2.739s
% 2.92/3.19  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.92/3.19  % SZS output start Refutation
% 2.92/3.19  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.92/3.19  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.92/3.19  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 2.92/3.19  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.92/3.19  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.92/3.19  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.92/3.19  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.92/3.19  thf(sk_B_type, type, sk_B: $i).
% 2.92/3.19  thf(sk_A_type, type, sk_A: $i).
% 2.92/3.19  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.92/3.19  thf(t73_xboole_1, conjecture,
% 2.92/3.19    (![A:$i,B:$i,C:$i]:
% 2.92/3.19     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 2.92/3.19       ( r1_tarski @ A @ B ) ))).
% 2.92/3.19  thf(zf_stmt_0, negated_conjecture,
% 2.92/3.19    (~( ![A:$i,B:$i,C:$i]:
% 2.92/3.19        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 2.92/3.19            ( r1_xboole_0 @ A @ C ) ) =>
% 2.92/3.19          ( r1_tarski @ A @ B ) ) )),
% 2.92/3.19    inference('cnf.neg', [status(esa)], [t73_xboole_1])).
% 2.92/3.19  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 2.92/3.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.19  thf(d3_tarski, axiom,
% 2.92/3.19    (![A:$i,B:$i]:
% 2.92/3.19     ( ( r1_tarski @ A @ B ) <=>
% 2.92/3.19       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.92/3.19  thf('1', plain,
% 2.92/3.19      (![X3 : $i, X5 : $i]:
% 2.92/3.19         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 2.92/3.19      inference('cnf', [status(esa)], [d3_tarski])).
% 2.92/3.19  thf('2', plain, ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))),
% 2.92/3.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.19  thf('3', plain,
% 2.92/3.19      (![X2 : $i, X3 : $i, X4 : $i]:
% 2.92/3.19         (~ (r2_hidden @ X2 @ X3)
% 2.92/3.19          | (r2_hidden @ X2 @ X4)
% 2.92/3.19          | ~ (r1_tarski @ X3 @ X4))),
% 2.92/3.19      inference('cnf', [status(esa)], [d3_tarski])).
% 2.92/3.19  thf('4', plain,
% 2.92/3.19      (![X0 : $i]:
% 2.92/3.19         ((r2_hidden @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_1))
% 2.92/3.19          | ~ (r2_hidden @ X0 @ sk_A))),
% 2.92/3.19      inference('sup-', [status(thm)], ['2', '3'])).
% 2.92/3.19  thf('5', plain,
% 2.92/3.19      (![X0 : $i]:
% 2.92/3.19         ((r1_tarski @ sk_A @ X0)
% 2.92/3.19          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 2.92/3.19      inference('sup-', [status(thm)], ['1', '4'])).
% 2.92/3.19  thf(d3_xboole_0, axiom,
% 2.92/3.19    (![A:$i,B:$i,C:$i]:
% 2.92/3.19     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 2.92/3.19       ( ![D:$i]:
% 2.92/3.19         ( ( r2_hidden @ D @ C ) <=>
% 2.92/3.19           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 2.92/3.19  thf('6', plain,
% 2.92/3.19      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 2.92/3.19         (~ (r2_hidden @ X10 @ X8)
% 2.92/3.19          | (r2_hidden @ X10 @ X9)
% 2.92/3.19          | (r2_hidden @ X10 @ X7)
% 2.92/3.19          | ((X8) != (k2_xboole_0 @ X9 @ X7)))),
% 2.92/3.19      inference('cnf', [status(esa)], [d3_xboole_0])).
% 2.92/3.19  thf('7', plain,
% 2.92/3.19      (![X7 : $i, X9 : $i, X10 : $i]:
% 2.92/3.19         ((r2_hidden @ X10 @ X7)
% 2.92/3.19          | (r2_hidden @ X10 @ X9)
% 2.92/3.19          | ~ (r2_hidden @ X10 @ (k2_xboole_0 @ X9 @ X7)))),
% 2.92/3.19      inference('simplify', [status(thm)], ['6'])).
% 2.92/3.19  thf('8', plain,
% 2.92/3.19      (![X0 : $i]:
% 2.92/3.19         ((r1_tarski @ sk_A @ X0)
% 2.92/3.19          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B)
% 2.92/3.19          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_C_1))),
% 2.92/3.19      inference('sup-', [status(thm)], ['5', '7'])).
% 2.92/3.19  thf('9', plain, ((r1_xboole_0 @ sk_A @ sk_C_1)),
% 2.92/3.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.19  thf(symmetry_r1_xboole_0, axiom,
% 2.92/3.19    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 2.92/3.19  thf('10', plain,
% 2.92/3.19      (![X12 : $i, X13 : $i]:
% 2.92/3.19         ((r1_xboole_0 @ X12 @ X13) | ~ (r1_xboole_0 @ X13 @ X12))),
% 2.92/3.19      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.92/3.19  thf('11', plain, ((r1_xboole_0 @ sk_C_1 @ sk_A)),
% 2.92/3.19      inference('sup-', [status(thm)], ['9', '10'])).
% 2.92/3.19  thf('12', plain,
% 2.92/3.19      (![X3 : $i, X5 : $i]:
% 2.92/3.19         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 2.92/3.19      inference('cnf', [status(esa)], [d3_tarski])).
% 2.92/3.19  thf('13', plain,
% 2.92/3.19      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 2.92/3.19         (~ (r2_hidden @ X6 @ X7)
% 2.92/3.19          | (r2_hidden @ X6 @ X8)
% 2.92/3.19          | ((X8) != (k2_xboole_0 @ X9 @ X7)))),
% 2.92/3.19      inference('cnf', [status(esa)], [d3_xboole_0])).
% 2.92/3.19  thf('14', plain,
% 2.92/3.19      (![X6 : $i, X7 : $i, X9 : $i]:
% 2.92/3.19         ((r2_hidden @ X6 @ (k2_xboole_0 @ X9 @ X7)) | ~ (r2_hidden @ X6 @ X7))),
% 2.92/3.19      inference('simplify', [status(thm)], ['13'])).
% 2.92/3.19  thf('15', plain,
% 2.92/3.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.92/3.19         ((r1_tarski @ X0 @ X1)
% 2.92/3.19          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_xboole_0 @ X2 @ X0)))),
% 2.92/3.19      inference('sup-', [status(thm)], ['12', '14'])).
% 2.92/3.19  thf(t5_xboole_0, axiom,
% 2.92/3.19    (![A:$i,B:$i,C:$i]:
% 2.92/3.19     ( ~( ( ~( ( ~( r2_hidden @ C @ A ) ) & ( r2_hidden @ C @ B ) ) ) & 
% 2.92/3.19          ( ~( ( ~( r2_hidden @ C @ B ) ) & ( r2_hidden @ C @ A ) ) ) & 
% 2.92/3.19          ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) ) & ( r1_xboole_0 @ A @ B ) ) ))).
% 2.92/3.19  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.92/3.19  thf(zf_stmt_2, axiom,
% 2.92/3.19    (![C:$i,B:$i,A:$i]:
% 2.92/3.19     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.92/3.19       ( ( r2_hidden @ C @ A ) & ( ~( r2_hidden @ C @ B ) ) ) ))).
% 2.92/3.19  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $i > $o).
% 2.92/3.19  thf(zf_stmt_4, axiom,
% 2.92/3.19    (![C:$i,B:$i,A:$i]:
% 2.92/3.19     ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 2.92/3.19       ( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ))).
% 2.92/3.19  thf(zf_stmt_5, axiom,
% 2.92/3.19    (![A:$i,B:$i,C:$i]:
% 2.92/3.19     ( ~( ( r1_xboole_0 @ A @ B ) & 
% 2.92/3.19          ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) ) & 
% 2.92/3.19          ( ~( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.92/3.19          ( ~( zip_tseitin_0 @ C @ B @ A ) ) ) ))).
% 2.92/3.19  thf('16', plain,
% 2.92/3.19      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.92/3.19         (~ (r1_xboole_0 @ X20 @ X21)
% 2.92/3.19          | (zip_tseitin_0 @ X22 @ X21 @ X20)
% 2.92/3.19          | (zip_tseitin_1 @ X22 @ X21 @ X20)
% 2.92/3.19          | ~ (r2_hidden @ X22 @ (k2_xboole_0 @ X20 @ X21)))),
% 2.92/3.19      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.92/3.19  thf('17', plain,
% 2.92/3.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.92/3.19         ((r1_tarski @ X0 @ X2)
% 2.92/3.19          | (zip_tseitin_1 @ (sk_C @ X2 @ X0) @ X0 @ X1)
% 2.92/3.19          | (zip_tseitin_0 @ (sk_C @ X2 @ X0) @ X0 @ X1)
% 2.92/3.19          | ~ (r1_xboole_0 @ X1 @ X0))),
% 2.92/3.19      inference('sup-', [status(thm)], ['15', '16'])).
% 2.92/3.19  thf('18', plain,
% 2.92/3.19      (![X0 : $i]:
% 2.92/3.19         ((zip_tseitin_0 @ (sk_C @ X0 @ sk_A) @ sk_A @ sk_C_1)
% 2.92/3.19          | (zip_tseitin_1 @ (sk_C @ X0 @ sk_A) @ sk_A @ sk_C_1)
% 2.92/3.19          | (r1_tarski @ sk_A @ X0))),
% 2.92/3.19      inference('sup-', [status(thm)], ['11', '17'])).
% 2.92/3.19  thf('19', plain,
% 2.92/3.19      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.92/3.19         (~ (r2_hidden @ X17 @ X19) | ~ (zip_tseitin_1 @ X17 @ X19 @ X18))),
% 2.92/3.19      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.92/3.19  thf('20', plain,
% 2.92/3.19      (![X0 : $i]:
% 2.92/3.19         ((r1_tarski @ sk_A @ X0)
% 2.92/3.19          | (zip_tseitin_0 @ (sk_C @ X0 @ sk_A) @ sk_A @ sk_C_1)
% 2.92/3.19          | ~ (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_A))),
% 2.92/3.19      inference('sup-', [status(thm)], ['18', '19'])).
% 2.92/3.19  thf('21', plain,
% 2.92/3.19      (![X3 : $i, X5 : $i]:
% 2.92/3.19         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 2.92/3.19      inference('cnf', [status(esa)], [d3_tarski])).
% 2.92/3.19  thf('22', plain,
% 2.92/3.19      (![X0 : $i]:
% 2.92/3.19         ((zip_tseitin_0 @ (sk_C @ X0 @ sk_A) @ sk_A @ sk_C_1)
% 2.92/3.19          | (r1_tarski @ sk_A @ X0))),
% 2.92/3.19      inference('clc', [status(thm)], ['20', '21'])).
% 2.92/3.19  thf('23', plain,
% 2.92/3.19      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.92/3.19         (~ (r2_hidden @ X14 @ X16) | ~ (zip_tseitin_0 @ X14 @ X15 @ X16))),
% 2.92/3.19      inference('cnf', [status(esa)], [zf_stmt_4])).
% 2.92/3.19  thf('24', plain,
% 2.92/3.19      (![X0 : $i]:
% 2.92/3.19         ((r1_tarski @ sk_A @ X0) | ~ (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_C_1))),
% 2.92/3.19      inference('sup-', [status(thm)], ['22', '23'])).
% 2.92/3.19  thf('25', plain,
% 2.92/3.19      (![X0 : $i]:
% 2.92/3.19         ((r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B)
% 2.92/3.19          | (r1_tarski @ sk_A @ X0)
% 2.92/3.19          | (r1_tarski @ sk_A @ X0))),
% 2.92/3.19      inference('sup-', [status(thm)], ['8', '24'])).
% 2.92/3.19  thf('26', plain,
% 2.92/3.19      (![X0 : $i]:
% 2.92/3.19         ((r1_tarski @ sk_A @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 2.92/3.19      inference('simplify', [status(thm)], ['25'])).
% 2.92/3.19  thf('27', plain,
% 2.92/3.19      (![X3 : $i, X5 : $i]:
% 2.92/3.19         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 2.92/3.19      inference('cnf', [status(esa)], [d3_tarski])).
% 2.92/3.19  thf('28', plain, (((r1_tarski @ sk_A @ sk_B) | (r1_tarski @ sk_A @ sk_B))),
% 2.92/3.19      inference('sup-', [status(thm)], ['26', '27'])).
% 2.92/3.19  thf('29', plain, ((r1_tarski @ sk_A @ sk_B)),
% 2.92/3.19      inference('simplify', [status(thm)], ['28'])).
% 2.92/3.19  thf('30', plain, ($false), inference('demod', [status(thm)], ['0', '29'])).
% 2.92/3.19  
% 2.92/3.19  % SZS output end Refutation
% 2.92/3.19  
% 3.04/3.20  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
