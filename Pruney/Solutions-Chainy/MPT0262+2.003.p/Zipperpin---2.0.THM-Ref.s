%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0B9C0A9bz1

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:30 EST 2020

% Result     : Theorem 0.89s
% Output     : Refutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :   45 (  68 expanded)
%              Number of leaves         :   12 (  24 expanded)
%              Depth                    :   12
%              Number of atoms          :  379 ( 660 expanded)
%              Number of equality atoms :   16 (  24 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t57_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ B )
        & ~ ( r2_hidden @ C @ B )
        & ~ ( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r2_hidden @ A @ B )
          & ~ ( r2_hidden @ C @ B )
          & ~ ( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t57_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('3',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('5',plain,(
    ! [X10: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X12 )
      | ( X14 = X13 )
      | ( X14 = X10 )
      | ( X12
       != ( k2_tarski @ X13 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('6',plain,(
    ! [X10: $i,X13: $i,X14: $i] :
      ( ( X14 = X10 )
      | ( X14 = X13 )
      | ~ ( r2_hidden @ X14 @ ( k2_tarski @ X13 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( ( sk_C @ ( k2_tarski @ X1 @ X0 ) @ X2 )
        = X1 )
      | ( ( sk_C @ ( k2_tarski @ X1 @ X0 ) @ X2 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('9',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('10',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( sk_C @ ( k2_tarski @ X0 @ X2 ) @ X1 )
        = X2 )
      | ( r1_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X2 ) )
      | ( r1_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['7','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X2 ) )
      | ( ( sk_C @ ( k2_tarski @ X0 @ X2 ) @ X1 )
        = X2 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X2 @ X1 )
      | ( r1_xboole_0 @ X1 @ ( k2_tarski @ X2 @ X0 ) )
      | ( r1_xboole_0 @ X1 @ ( k2_tarski @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k2_tarski @ X2 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X6 @ X9 ) )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X1 @ X2 )
      | ( r1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['16','25'])).

thf('27',plain,(
    ~ ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['0','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0B9C0A9bz1
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:43:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.21/0.36  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 0.89/1.11  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.89/1.11  % Solved by: fo/fo7.sh
% 0.89/1.11  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.89/1.11  % done 1076 iterations in 0.641s
% 0.89/1.11  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.89/1.11  % SZS output start Refutation
% 0.89/1.11  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.89/1.11  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.89/1.11  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.89/1.11  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.89/1.11  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.89/1.11  thf(sk_B_type, type, sk_B: $i).
% 0.89/1.11  thf(sk_A_type, type, sk_A: $i).
% 0.89/1.11  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.89/1.11  thf(t57_zfmisc_1, conjecture,
% 0.89/1.11    (![A:$i,B:$i,C:$i]:
% 0.89/1.11     ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ~( r2_hidden @ C @ B ) ) & 
% 0.89/1.11          ( ~( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) ) ))).
% 0.89/1.11  thf(zf_stmt_0, negated_conjecture,
% 0.89/1.11    (~( ![A:$i,B:$i,C:$i]:
% 0.89/1.11        ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ~( r2_hidden @ C @ B ) ) & 
% 0.89/1.11             ( ~( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) ) ) )),
% 0.89/1.11    inference('cnf.neg', [status(esa)], [t57_zfmisc_1])).
% 0.89/1.11  thf('0', plain, (~ (r2_hidden @ sk_C_1 @ sk_B)),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf(t4_xboole_0, axiom,
% 0.89/1.11    (![A:$i,B:$i]:
% 0.89/1.11     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.89/1.11            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.89/1.11       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.89/1.11            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.89/1.11  thf('1', plain,
% 0.89/1.11      (![X6 : $i, X7 : $i]:
% 0.89/1.11         ((r1_xboole_0 @ X6 @ X7)
% 0.89/1.11          | (r2_hidden @ (sk_C @ X7 @ X6) @ (k3_xboole_0 @ X6 @ X7)))),
% 0.89/1.11      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.89/1.11  thf(d4_xboole_0, axiom,
% 0.89/1.11    (![A:$i,B:$i,C:$i]:
% 0.89/1.11     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.89/1.11       ( ![D:$i]:
% 0.89/1.11         ( ( r2_hidden @ D @ C ) <=>
% 0.89/1.11           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.89/1.11  thf('2', plain,
% 0.89/1.11      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.89/1.11         (~ (r2_hidden @ X4 @ X3)
% 0.89/1.11          | (r2_hidden @ X4 @ X2)
% 0.89/1.11          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.89/1.11      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.89/1.11  thf('3', plain,
% 0.89/1.11      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.89/1.11         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.89/1.11      inference('simplify', [status(thm)], ['2'])).
% 0.89/1.11  thf('4', plain,
% 0.89/1.11      (![X0 : $i, X1 : $i]:
% 0.89/1.11         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C @ X0 @ X1) @ X0))),
% 0.89/1.11      inference('sup-', [status(thm)], ['1', '3'])).
% 0.89/1.11  thf(d2_tarski, axiom,
% 0.89/1.11    (![A:$i,B:$i,C:$i]:
% 0.89/1.11     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.89/1.11       ( ![D:$i]:
% 0.89/1.11         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.89/1.11  thf('5', plain,
% 0.89/1.11      (![X10 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.89/1.11         (~ (r2_hidden @ X14 @ X12)
% 0.89/1.11          | ((X14) = (X13))
% 0.89/1.11          | ((X14) = (X10))
% 0.89/1.11          | ((X12) != (k2_tarski @ X13 @ X10)))),
% 0.89/1.11      inference('cnf', [status(esa)], [d2_tarski])).
% 0.89/1.11  thf('6', plain,
% 0.89/1.11      (![X10 : $i, X13 : $i, X14 : $i]:
% 0.89/1.11         (((X14) = (X10))
% 0.89/1.11          | ((X14) = (X13))
% 0.89/1.11          | ~ (r2_hidden @ X14 @ (k2_tarski @ X13 @ X10)))),
% 0.89/1.11      inference('simplify', [status(thm)], ['5'])).
% 0.89/1.11  thf('7', plain,
% 0.89/1.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.11         ((r1_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0))
% 0.89/1.11          | ((sk_C @ (k2_tarski @ X1 @ X0) @ X2) = (X1))
% 0.89/1.11          | ((sk_C @ (k2_tarski @ X1 @ X0) @ X2) = (X0)))),
% 0.89/1.11      inference('sup-', [status(thm)], ['4', '6'])).
% 0.89/1.11  thf('8', plain,
% 0.89/1.11      (![X6 : $i, X7 : $i]:
% 0.89/1.11         ((r1_xboole_0 @ X6 @ X7)
% 0.89/1.11          | (r2_hidden @ (sk_C @ X7 @ X6) @ (k3_xboole_0 @ X6 @ X7)))),
% 0.89/1.11      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.89/1.11  thf('9', plain,
% 0.89/1.11      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.89/1.11         (~ (r2_hidden @ X4 @ X3)
% 0.89/1.11          | (r2_hidden @ X4 @ X1)
% 0.89/1.11          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.89/1.11      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.89/1.11  thf('10', plain,
% 0.89/1.11      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.89/1.11         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.89/1.11      inference('simplify', [status(thm)], ['9'])).
% 0.89/1.11  thf('11', plain,
% 0.89/1.11      (![X0 : $i, X1 : $i]:
% 0.89/1.11         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.89/1.11      inference('sup-', [status(thm)], ['8', '10'])).
% 0.89/1.11  thf('12', plain,
% 0.89/1.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.11         ((r2_hidden @ X0 @ X1)
% 0.89/1.11          | ((sk_C @ (k2_tarski @ X0 @ X2) @ X1) = (X2))
% 0.89/1.11          | (r1_xboole_0 @ X1 @ (k2_tarski @ X0 @ X2))
% 0.89/1.11          | (r1_xboole_0 @ X1 @ (k2_tarski @ X0 @ X2)))),
% 0.89/1.11      inference('sup+', [status(thm)], ['7', '11'])).
% 0.89/1.11  thf('13', plain,
% 0.89/1.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.11         ((r1_xboole_0 @ X1 @ (k2_tarski @ X0 @ X2))
% 0.89/1.11          | ((sk_C @ (k2_tarski @ X0 @ X2) @ X1) = (X2))
% 0.89/1.11          | (r2_hidden @ X0 @ X1))),
% 0.89/1.11      inference('simplify', [status(thm)], ['12'])).
% 0.89/1.11  thf('14', plain,
% 0.89/1.11      (![X0 : $i, X1 : $i]:
% 0.89/1.11         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.89/1.11      inference('sup-', [status(thm)], ['8', '10'])).
% 0.89/1.11  thf('15', plain,
% 0.89/1.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.11         ((r2_hidden @ X0 @ X1)
% 0.89/1.11          | (r2_hidden @ X2 @ X1)
% 0.89/1.11          | (r1_xboole_0 @ X1 @ (k2_tarski @ X2 @ X0))
% 0.89/1.11          | (r1_xboole_0 @ X1 @ (k2_tarski @ X2 @ X0)))),
% 0.89/1.11      inference('sup+', [status(thm)], ['13', '14'])).
% 0.89/1.11  thf('16', plain,
% 0.89/1.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.11         ((r1_xboole_0 @ X1 @ (k2_tarski @ X2 @ X0))
% 0.89/1.11          | (r2_hidden @ X2 @ X1)
% 0.89/1.11          | (r2_hidden @ X0 @ X1))),
% 0.89/1.11      inference('simplify', [status(thm)], ['15'])).
% 0.89/1.11  thf('17', plain,
% 0.89/1.11      (![X0 : $i, X1 : $i]:
% 0.89/1.11         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C @ X0 @ X1) @ X0))),
% 0.89/1.11      inference('sup-', [status(thm)], ['1', '3'])).
% 0.89/1.11  thf('18', plain,
% 0.89/1.11      (![X0 : $i, X1 : $i]:
% 0.89/1.11         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.89/1.11      inference('sup-', [status(thm)], ['8', '10'])).
% 0.89/1.11  thf('19', plain,
% 0.89/1.11      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.89/1.11         (~ (r2_hidden @ X0 @ X1)
% 0.89/1.11          | ~ (r2_hidden @ X0 @ X2)
% 0.89/1.11          | (r2_hidden @ X0 @ X3)
% 0.89/1.11          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.89/1.11      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.89/1.11  thf('20', plain,
% 0.89/1.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.11         ((r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 0.89/1.11          | ~ (r2_hidden @ X0 @ X2)
% 0.89/1.11          | ~ (r2_hidden @ X0 @ X1))),
% 0.89/1.11      inference('simplify', [status(thm)], ['19'])).
% 0.89/1.11  thf('21', plain,
% 0.89/1.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.11         ((r1_xboole_0 @ X0 @ X1)
% 0.89/1.11          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 0.89/1.11          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_xboole_0 @ X2 @ X0)))),
% 0.89/1.11      inference('sup-', [status(thm)], ['18', '20'])).
% 0.89/1.11  thf('22', plain,
% 0.89/1.11      (![X0 : $i, X1 : $i]:
% 0.89/1.11         ((r1_xboole_0 @ X1 @ X0)
% 0.89/1.11          | (r2_hidden @ (sk_C @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1))
% 0.89/1.11          | (r1_xboole_0 @ X1 @ X0))),
% 0.89/1.11      inference('sup-', [status(thm)], ['17', '21'])).
% 0.89/1.11  thf('23', plain,
% 0.89/1.11      (![X0 : $i, X1 : $i]:
% 0.89/1.11         ((r2_hidden @ (sk_C @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1))
% 0.89/1.11          | (r1_xboole_0 @ X1 @ X0))),
% 0.89/1.11      inference('simplify', [status(thm)], ['22'])).
% 0.89/1.11  thf('24', plain,
% 0.89/1.11      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.89/1.11         (~ (r2_hidden @ X8 @ (k3_xboole_0 @ X6 @ X9))
% 0.89/1.11          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.89/1.11      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.89/1.11  thf('25', plain,
% 0.89/1.11      (![X0 : $i, X1 : $i]:
% 0.89/1.11         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.89/1.11      inference('sup-', [status(thm)], ['23', '24'])).
% 0.89/1.11  thf('26', plain,
% 0.89/1.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.11         ((r2_hidden @ X0 @ X2)
% 0.89/1.11          | (r2_hidden @ X1 @ X2)
% 0.89/1.11          | (r1_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2))),
% 0.89/1.11      inference('sup-', [status(thm)], ['16', '25'])).
% 0.89/1.11  thf('27', plain, (~ (r1_xboole_0 @ (k2_tarski @ sk_A @ sk_C_1) @ sk_B)),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('28', plain, (((r2_hidden @ sk_A @ sk_B) | (r2_hidden @ sk_C_1 @ sk_B))),
% 0.89/1.11      inference('sup-', [status(thm)], ['26', '27'])).
% 0.89/1.11  thf('29', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('30', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.89/1.11      inference('clc', [status(thm)], ['28', '29'])).
% 0.89/1.11  thf('31', plain, ($false), inference('demod', [status(thm)], ['0', '30'])).
% 0.89/1.11  
% 0.89/1.11  % SZS output end Refutation
% 0.89/1.11  
% 0.89/1.12  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
