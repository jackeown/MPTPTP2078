%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5ULFR80Nm8

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:44 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 145 expanded)
%              Number of leaves         :   22 (  56 expanded)
%              Depth                    :   14
%              Number of atoms          :  331 (1073 expanded)
%              Number of equality atoms :    4 (  18 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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

thf('1',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_xboole_0 @ X16 @ X17 )
      | ( r1_xboole_0 @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_C @ X0 )
      | ~ ( r1_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_xboole_0 @ sk_C @ sk_B_1 ),
    inference('sup-',[status(thm)],['0','3'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('6',plain,(
    r1_xboole_0 @ sk_B_1 @ sk_C ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    r1_tarski @ sk_C @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_xboole_0 @ X16 @ X17 )
      | ( r1_xboole_0 @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_C @ X0 )
      | ~ ( r1_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r1_xboole_0 @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['6','9'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('11',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

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

thf('12',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_xboole_0 @ X12 @ X13 )
      | ( zip_tseitin_0 @ X14 @ X13 @ X12 )
      | ( zip_tseitin_1 @ X14 @ X13 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( zip_tseitin_1 @ ( sk_B @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X0 @ X1 )
      | ( zip_tseitin_0 @ ( sk_B @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( zip_tseitin_0 @ ( sk_B @ ( k2_xboole_0 @ sk_C @ sk_C ) ) @ sk_C @ sk_C )
    | ( zip_tseitin_1 @ ( sk_B @ ( k2_xboole_0 @ sk_C @ sk_C ) ) @ sk_C @ sk_C )
    | ( v1_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('15',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('16',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('17',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('18',plain,
    ( ( zip_tseitin_0 @ ( sk_B @ sk_C ) @ sk_C @ sk_C )
    | ( zip_tseitin_1 @ ( sk_B @ sk_C ) @ sk_C @ sk_C )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['14','15','16','17'])).

thf('19',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( zip_tseitin_1 @ ( sk_B @ sk_C ) @ sk_C @ sk_C )
    | ( zip_tseitin_0 @ ( sk_B @ sk_C ) @ sk_C @ sk_C ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X11 )
      | ~ ( zip_tseitin_1 @ X9 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('22',plain,
    ( ( zip_tseitin_0 @ ( sk_B @ sk_C ) @ sk_C @ sk_C )
    | ~ ( r2_hidden @ ( sk_B @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( zip_tseitin_1 @ ( sk_B @ sk_C ) @ sk_C @ sk_C )
    | ( zip_tseitin_0 @ ( sk_B @ sk_C ) @ sk_C @ sk_C ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('24',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ~ ( zip_tseitin_1 @ X9 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('25',plain,
    ( ( zip_tseitin_0 @ ( sk_B @ sk_C ) @ sk_C @ sk_C )
    | ( r2_hidden @ ( sk_B @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ~ ( zip_tseitin_0 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('27',plain,(
    r2_hidden @ ( sk_B @ sk_C ) @ sk_C ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    zip_tseitin_0 @ ( sk_B @ sk_C ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( zip_tseitin_0 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('30',plain,(
    ~ ( r2_hidden @ ( sk_B @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r2_hidden @ ( sk_B @ sk_C ) @ sk_C ),
    inference(clc,[status(thm)],['25','26'])).

thf('32',plain,(
    $false ),
    inference(demod,[status(thm)],['30','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5ULFR80Nm8
% 0.15/0.36  % Computer   : n002.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 10:24:22 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 0.23/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.49  % Solved by: fo/fo7.sh
% 0.23/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.49  % done 33 iterations in 0.016s
% 0.23/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.49  % SZS output start Refutation
% 0.23/0.49  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.23/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.23/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.23/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.23/0.49  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.23/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.23/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.49  thf(t68_xboole_1, conjecture,
% 0.23/0.49    (![A:$i,B:$i,C:$i]:
% 0.23/0.49     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.23/0.49       ( ~( ( r1_tarski @ C @ A ) & ( r1_tarski @ C @ B ) & 
% 0.23/0.49            ( r1_xboole_0 @ A @ B ) ) ) ))).
% 0.23/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.23/0.49        ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.23/0.49          ( ~( ( r1_tarski @ C @ A ) & ( r1_tarski @ C @ B ) & 
% 0.23/0.49               ( r1_xboole_0 @ A @ B ) ) ) ) )),
% 0.23/0.49    inference('cnf.neg', [status(esa)], [t68_xboole_1])).
% 0.23/0.49  thf('0', plain, ((r1_xboole_0 @ sk_A @ sk_B_1)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('1', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf(t63_xboole_1, axiom,
% 0.23/0.49    (![A:$i,B:$i,C:$i]:
% 0.23/0.49     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.23/0.49       ( r1_xboole_0 @ A @ C ) ))).
% 0.23/0.49  thf('2', plain,
% 0.23/0.49      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.23/0.49         (~ (r1_tarski @ X15 @ X16)
% 0.23/0.49          | ~ (r1_xboole_0 @ X16 @ X17)
% 0.23/0.49          | (r1_xboole_0 @ X15 @ X17))),
% 0.23/0.49      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.23/0.49  thf('3', plain,
% 0.23/0.49      (![X0 : $i]: ((r1_xboole_0 @ sk_C @ X0) | ~ (r1_xboole_0 @ sk_A @ X0))),
% 0.23/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.49  thf('4', plain, ((r1_xboole_0 @ sk_C @ sk_B_1)),
% 0.23/0.49      inference('sup-', [status(thm)], ['0', '3'])).
% 0.23/0.49  thf(symmetry_r1_xboole_0, axiom,
% 0.23/0.49    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.23/0.49  thf('5', plain,
% 0.23/0.49      (![X4 : $i, X5 : $i]:
% 0.23/0.49         ((r1_xboole_0 @ X4 @ X5) | ~ (r1_xboole_0 @ X5 @ X4))),
% 0.23/0.49      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.23/0.49  thf('6', plain, ((r1_xboole_0 @ sk_B_1 @ sk_C)),
% 0.23/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.23/0.49  thf('7', plain, ((r1_tarski @ sk_C @ sk_B_1)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('8', plain,
% 0.23/0.49      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.23/0.49         (~ (r1_tarski @ X15 @ X16)
% 0.23/0.49          | ~ (r1_xboole_0 @ X16 @ X17)
% 0.23/0.49          | (r1_xboole_0 @ X15 @ X17))),
% 0.23/0.49      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.23/0.49  thf('9', plain,
% 0.23/0.49      (![X0 : $i]: ((r1_xboole_0 @ sk_C @ X0) | ~ (r1_xboole_0 @ sk_B_1 @ X0))),
% 0.23/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.23/0.49  thf('10', plain, ((r1_xboole_0 @ sk_C @ sk_C)),
% 0.23/0.49      inference('sup-', [status(thm)], ['6', '9'])).
% 0.23/0.49  thf(d1_xboole_0, axiom,
% 0.23/0.49    (![A:$i]:
% 0.23/0.49     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.23/0.49  thf('11', plain,
% 0.23/0.49      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.23/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.23/0.49  thf(t5_xboole_0, axiom,
% 0.23/0.49    (![A:$i,B:$i,C:$i]:
% 0.23/0.49     ( ~( ( ~( ( ~( r2_hidden @ C @ A ) ) & ( r2_hidden @ C @ B ) ) ) & 
% 0.23/0.49          ( ~( ( ~( r2_hidden @ C @ B ) ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.23/0.49          ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) ) & ( r1_xboole_0 @ A @ B ) ) ))).
% 0.23/0.49  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.23/0.49  thf(zf_stmt_2, axiom,
% 0.23/0.49    (![C:$i,B:$i,A:$i]:
% 0.23/0.49     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.23/0.49       ( ( r2_hidden @ C @ A ) & ( ~( r2_hidden @ C @ B ) ) ) ))).
% 0.23/0.49  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.23/0.49  thf(zf_stmt_4, axiom,
% 0.23/0.49    (![C:$i,B:$i,A:$i]:
% 0.23/0.49     ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.23/0.49       ( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ))).
% 0.23/0.49  thf(zf_stmt_5, axiom,
% 0.23/0.49    (![A:$i,B:$i,C:$i]:
% 0.23/0.49     ( ~( ( r1_xboole_0 @ A @ B ) & 
% 0.23/0.49          ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) ) & 
% 0.23/0.49          ( ~( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.23/0.49          ( ~( zip_tseitin_0 @ C @ B @ A ) ) ) ))).
% 0.23/0.49  thf('12', plain,
% 0.23/0.49      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.23/0.49         (~ (r1_xboole_0 @ X12 @ X13)
% 0.23/0.49          | (zip_tseitin_0 @ X14 @ X13 @ X12)
% 0.23/0.49          | (zip_tseitin_1 @ X14 @ X13 @ X12)
% 0.23/0.49          | ~ (r2_hidden @ X14 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.23/0.49  thf('13', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i]:
% 0.23/0.49         ((v1_xboole_0 @ (k2_xboole_0 @ X1 @ X0))
% 0.23/0.49          | (zip_tseitin_1 @ (sk_B @ (k2_xboole_0 @ X1 @ X0)) @ X0 @ X1)
% 0.23/0.49          | (zip_tseitin_0 @ (sk_B @ (k2_xboole_0 @ X1 @ X0)) @ X0 @ X1)
% 0.23/0.49          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.23/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.23/0.49  thf('14', plain,
% 0.23/0.49      (((zip_tseitin_0 @ (sk_B @ (k2_xboole_0 @ sk_C @ sk_C)) @ sk_C @ sk_C)
% 0.23/0.49        | (zip_tseitin_1 @ (sk_B @ (k2_xboole_0 @ sk_C @ sk_C)) @ sk_C @ sk_C)
% 0.23/0.49        | (v1_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_C)))),
% 0.23/0.49      inference('sup-', [status(thm)], ['10', '13'])).
% 0.23/0.49  thf(idempotence_k2_xboole_0, axiom,
% 0.23/0.49    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.23/0.49  thf('15', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ X3) = (X3))),
% 0.23/0.49      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.23/0.49  thf('16', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ X3) = (X3))),
% 0.23/0.49      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.23/0.49  thf('17', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ X3) = (X3))),
% 0.23/0.49      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.23/0.49  thf('18', plain,
% 0.23/0.49      (((zip_tseitin_0 @ (sk_B @ sk_C) @ sk_C @ sk_C)
% 0.23/0.49        | (zip_tseitin_1 @ (sk_B @ sk_C) @ sk_C @ sk_C)
% 0.23/0.49        | (v1_xboole_0 @ sk_C))),
% 0.23/0.49      inference('demod', [status(thm)], ['14', '15', '16', '17'])).
% 0.23/0.49  thf('19', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('20', plain,
% 0.23/0.49      (((zip_tseitin_1 @ (sk_B @ sk_C) @ sk_C @ sk_C)
% 0.23/0.49        | (zip_tseitin_0 @ (sk_B @ sk_C) @ sk_C @ sk_C))),
% 0.23/0.49      inference('clc', [status(thm)], ['18', '19'])).
% 0.23/0.49  thf('21', plain,
% 0.23/0.49      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.23/0.49         (~ (r2_hidden @ X9 @ X11) | ~ (zip_tseitin_1 @ X9 @ X11 @ X10))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.23/0.49  thf('22', plain,
% 0.23/0.49      (((zip_tseitin_0 @ (sk_B @ sk_C) @ sk_C @ sk_C)
% 0.23/0.49        | ~ (r2_hidden @ (sk_B @ sk_C) @ sk_C))),
% 0.23/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.23/0.49  thf('23', plain,
% 0.23/0.49      (((zip_tseitin_1 @ (sk_B @ sk_C) @ sk_C @ sk_C)
% 0.23/0.49        | (zip_tseitin_0 @ (sk_B @ sk_C) @ sk_C @ sk_C))),
% 0.23/0.49      inference('clc', [status(thm)], ['18', '19'])).
% 0.23/0.49  thf('24', plain,
% 0.23/0.49      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.23/0.49         ((r2_hidden @ X9 @ X10) | ~ (zip_tseitin_1 @ X9 @ X11 @ X10))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.23/0.49  thf('25', plain,
% 0.23/0.49      (((zip_tseitin_0 @ (sk_B @ sk_C) @ sk_C @ sk_C)
% 0.23/0.49        | (r2_hidden @ (sk_B @ sk_C) @ sk_C))),
% 0.23/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.23/0.49  thf('26', plain,
% 0.23/0.49      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.23/0.49         ((r2_hidden @ X6 @ X7) | ~ (zip_tseitin_0 @ X6 @ X7 @ X8))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.23/0.49  thf('27', plain, ((r2_hidden @ (sk_B @ sk_C) @ sk_C)),
% 0.23/0.49      inference('clc', [status(thm)], ['25', '26'])).
% 0.23/0.49  thf('28', plain, ((zip_tseitin_0 @ (sk_B @ sk_C) @ sk_C @ sk_C)),
% 0.23/0.49      inference('demod', [status(thm)], ['22', '27'])).
% 0.23/0.49  thf('29', plain,
% 0.23/0.49      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.23/0.49         (~ (r2_hidden @ X6 @ X8) | ~ (zip_tseitin_0 @ X6 @ X7 @ X8))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.23/0.49  thf('30', plain, (~ (r2_hidden @ (sk_B @ sk_C) @ sk_C)),
% 0.23/0.49      inference('sup-', [status(thm)], ['28', '29'])).
% 0.23/0.49  thf('31', plain, ((r2_hidden @ (sk_B @ sk_C) @ sk_C)),
% 0.23/0.49      inference('clc', [status(thm)], ['25', '26'])).
% 0.23/0.49  thf('32', plain, ($false), inference('demod', [status(thm)], ['30', '31'])).
% 0.23/0.49  
% 0.23/0.49  % SZS output end Refutation
% 0.23/0.49  
% 0.23/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
