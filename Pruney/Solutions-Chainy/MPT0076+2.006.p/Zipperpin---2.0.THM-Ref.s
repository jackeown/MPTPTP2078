%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.m2L4QBmUEF

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:47 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   45 (  52 expanded)
%              Number of leaves         :   21 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :  248 ( 301 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('4',plain,(
    r1_xboole_0 @ sk_A @ sk_B_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_xboole_0 @ X16 @ X17 )
      | ( r1_xboole_0 @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ~ ( r1_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_xboole_0 @ sk_B_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('10',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_xboole_0 @ X12 @ X13 )
      | ( zip_tseitin_0 @ X14 @ X13 @ X12 )
      | ( zip_tseitin_1 @ X14 @ X13 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( zip_tseitin_1 @ X1 @ X0 @ X0 )
      | ( zip_tseitin_0 @ X1 @ X0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( zip_tseitin_0 @ ( sk_B @ X0 ) @ X0 @ X0 )
      | ( zip_tseitin_1 @ ( sk_B @ X0 ) @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,
    ( ( zip_tseitin_1 @ ( sk_B @ sk_B_1 ) @ sk_B_1 @ sk_B_1 )
    | ( zip_tseitin_0 @ ( sk_B @ sk_B_1 ) @ sk_B_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( zip_tseitin_0 @ ( sk_B @ sk_B_1 ) @ sk_B_1 @ sk_B_1 )
    | ( zip_tseitin_1 @ ( sk_B @ sk_B_1 ) @ sk_B_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X11 )
      | ~ ( zip_tseitin_1 @ X9 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('18',plain,
    ( ( zip_tseitin_0 @ ( sk_B @ sk_B_1 ) @ sk_B_1 @ sk_B_1 )
    | ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( zip_tseitin_0 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('20',plain,(
    ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['1','20'])).

thf('22',plain,(
    $false ),
    inference(demod,[status(thm)],['0','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.m2L4QBmUEF
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:16:11 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.45  % Solved by: fo/fo7.sh
% 0.19/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.45  % done 22 iterations in 0.013s
% 0.19/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.45  % SZS output start Refutation
% 0.19/0.45  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.45  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.45  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.45  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.19/0.45  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.45  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.45  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.19/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.45  thf(t69_xboole_1, conjecture,
% 0.19/0.45    (![A:$i,B:$i]:
% 0.19/0.45     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.19/0.45       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.19/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.45    (~( ![A:$i,B:$i]:
% 0.19/0.45        ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.19/0.45          ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) )),
% 0.19/0.45    inference('cnf.neg', [status(esa)], [t69_xboole_1])).
% 0.19/0.45  thf('0', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf(d1_xboole_0, axiom,
% 0.19/0.45    (![A:$i]:
% 0.19/0.45     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.19/0.45  thf('1', plain,
% 0.19/0.45      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.19/0.45      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.45  thf('2', plain, ((r1_xboole_0 @ sk_B_1 @ sk_A)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf(symmetry_r1_xboole_0, axiom,
% 0.19/0.45    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.19/0.45  thf('3', plain,
% 0.19/0.45      (![X4 : $i, X5 : $i]:
% 0.19/0.45         ((r1_xboole_0 @ X4 @ X5) | ~ (r1_xboole_0 @ X5 @ X4))),
% 0.19/0.45      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.19/0.45  thf('4', plain, ((r1_xboole_0 @ sk_A @ sk_B_1)),
% 0.19/0.45      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.45  thf('5', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf(t63_xboole_1, axiom,
% 0.19/0.45    (![A:$i,B:$i,C:$i]:
% 0.19/0.45     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.19/0.45       ( r1_xboole_0 @ A @ C ) ))).
% 0.19/0.45  thf('6', plain,
% 0.19/0.45      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.19/0.45         (~ (r1_tarski @ X15 @ X16)
% 0.19/0.45          | ~ (r1_xboole_0 @ X16 @ X17)
% 0.19/0.45          | (r1_xboole_0 @ X15 @ X17))),
% 0.19/0.45      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.19/0.45  thf('7', plain,
% 0.19/0.45      (![X0 : $i]: ((r1_xboole_0 @ sk_B_1 @ X0) | ~ (r1_xboole_0 @ sk_A @ X0))),
% 0.19/0.45      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.45  thf('8', plain, ((r1_xboole_0 @ sk_B_1 @ sk_B_1)),
% 0.19/0.45      inference('sup-', [status(thm)], ['4', '7'])).
% 0.19/0.45  thf('9', plain,
% 0.19/0.45      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.19/0.45      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.45  thf(idempotence_k2_xboole_0, axiom,
% 0.19/0.45    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.19/0.45  thf('10', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ X3) = (X3))),
% 0.19/0.45      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.19/0.45  thf(t5_xboole_0, axiom,
% 0.19/0.45    (![A:$i,B:$i,C:$i]:
% 0.19/0.45     ( ~( ( ~( ( ~( r2_hidden @ C @ A ) ) & ( r2_hidden @ C @ B ) ) ) & 
% 0.19/0.45          ( ~( ( ~( r2_hidden @ C @ B ) ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.19/0.45          ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) ) & ( r1_xboole_0 @ A @ B ) ) ))).
% 0.19/0.45  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.19/0.45  thf(zf_stmt_2, axiom,
% 0.19/0.45    (![C:$i,B:$i,A:$i]:
% 0.19/0.45     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.19/0.45       ( ( r2_hidden @ C @ A ) & ( ~( r2_hidden @ C @ B ) ) ) ))).
% 0.19/0.45  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.19/0.45  thf(zf_stmt_4, axiom,
% 0.19/0.45    (![C:$i,B:$i,A:$i]:
% 0.19/0.45     ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.19/0.45       ( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ))).
% 0.19/0.45  thf(zf_stmt_5, axiom,
% 0.19/0.45    (![A:$i,B:$i,C:$i]:
% 0.19/0.45     ( ~( ( r1_xboole_0 @ A @ B ) & 
% 0.19/0.45          ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) ) & 
% 0.19/0.45          ( ~( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.19/0.45          ( ~( zip_tseitin_0 @ C @ B @ A ) ) ) ))).
% 0.19/0.45  thf('11', plain,
% 0.19/0.45      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.45         (~ (r1_xboole_0 @ X12 @ X13)
% 0.19/0.45          | (zip_tseitin_0 @ X14 @ X13 @ X12)
% 0.19/0.45          | (zip_tseitin_1 @ X14 @ X13 @ X12)
% 0.19/0.45          | ~ (r2_hidden @ X14 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.19/0.45  thf('12', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i]:
% 0.19/0.45         (~ (r2_hidden @ X1 @ X0)
% 0.19/0.45          | (zip_tseitin_1 @ X1 @ X0 @ X0)
% 0.19/0.45          | (zip_tseitin_0 @ X1 @ X0 @ X0)
% 0.19/0.45          | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.19/0.45      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.45  thf('13', plain,
% 0.19/0.45      (![X0 : $i]:
% 0.19/0.45         ((v1_xboole_0 @ X0)
% 0.19/0.45          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.19/0.45          | (zip_tseitin_0 @ (sk_B @ X0) @ X0 @ X0)
% 0.19/0.45          | (zip_tseitin_1 @ (sk_B @ X0) @ X0 @ X0))),
% 0.19/0.45      inference('sup-', [status(thm)], ['9', '12'])).
% 0.19/0.45  thf('14', plain,
% 0.19/0.45      (((zip_tseitin_1 @ (sk_B @ sk_B_1) @ sk_B_1 @ sk_B_1)
% 0.19/0.45        | (zip_tseitin_0 @ (sk_B @ sk_B_1) @ sk_B_1 @ sk_B_1)
% 0.19/0.45        | (v1_xboole_0 @ sk_B_1))),
% 0.19/0.45      inference('sup-', [status(thm)], ['8', '13'])).
% 0.19/0.45  thf('15', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('16', plain,
% 0.19/0.45      (((zip_tseitin_0 @ (sk_B @ sk_B_1) @ sk_B_1 @ sk_B_1)
% 0.19/0.45        | (zip_tseitin_1 @ (sk_B @ sk_B_1) @ sk_B_1 @ sk_B_1))),
% 0.19/0.45      inference('clc', [status(thm)], ['14', '15'])).
% 0.19/0.45  thf('17', plain,
% 0.19/0.45      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.19/0.45         (~ (r2_hidden @ X9 @ X11) | ~ (zip_tseitin_1 @ X9 @ X11 @ X10))),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.19/0.45  thf('18', plain,
% 0.19/0.45      (((zip_tseitin_0 @ (sk_B @ sk_B_1) @ sk_B_1 @ sk_B_1)
% 0.19/0.45        | ~ (r2_hidden @ (sk_B @ sk_B_1) @ sk_B_1))),
% 0.19/0.45      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.45  thf('19', plain,
% 0.19/0.45      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.45         (~ (r2_hidden @ X6 @ X8) | ~ (zip_tseitin_0 @ X6 @ X7 @ X8))),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.19/0.45  thf('20', plain, (~ (r2_hidden @ (sk_B @ sk_B_1) @ sk_B_1)),
% 0.19/0.45      inference('clc', [status(thm)], ['18', '19'])).
% 0.19/0.45  thf('21', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.19/0.45      inference('sup-', [status(thm)], ['1', '20'])).
% 0.19/0.45  thf('22', plain, ($false), inference('demod', [status(thm)], ['0', '21'])).
% 0.19/0.45  
% 0.19/0.45  % SZS output end Refutation
% 0.19/0.45  
% 0.19/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
