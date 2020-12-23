%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.emCT099Z3i

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:22 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   60 (  66 expanded)
%              Number of leaves         :   28 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :  425 ( 491 expanded)
%              Number of equality atoms :   54 (  64 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t25_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        & ( A != B )
        & ( A != C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
          & ( A != B )
          & ( A != C ) ) ),
    inference('cnf.neg',[status(esa)],[t25_zfmisc_1])).

thf('0',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('2',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('4',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('5',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('6',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_enumset1 @ X40 @ X40 @ X41 )
      = ( k2_tarski @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('8',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( k2_enumset1 @ X35 @ X36 @ X37 @ X38 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X35 @ X36 @ X37 ) @ ( k1_tarski @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('10',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( k2_enumset1 @ X42 @ X42 @ X43 @ X44 )
      = ( k1_enumset1 @ X42 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t98_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ A @ C @ B ) ) )).

thf('11',plain,(
    ! [X67: $i,X68: $i,X69: $i] :
      ( ( k1_enumset1 @ X67 @ X69 @ X68 )
      = ( k1_enumset1 @ X67 @ X68 @ X69 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X0 @ X1 )
      = ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X67: $i,X68: $i,X69: $i] :
      ( ( k1_enumset1 @ X67 @ X69 @ X68 )
      = ( k1_enumset1 @ X67 @ X68 @ X69 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf(t102_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ C @ B @ A ) ) )).

thf('14',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X34 @ X33 @ X32 )
      = ( k1_enumset1 @ X32 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X34 @ X33 @ X32 )
      = ( k1_enumset1 @ X32 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X2 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['6','9','12','17'])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 )
      | ( r2_hidden @ X19 @ X23 )
      | ( X23
       != ( k1_enumset1 @ X22 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('20',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ X19 @ ( k1_enumset1 @ X22 @ X21 @ X20 ) )
      | ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ sk_B @ sk_C ) )
      | ( zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['18','20'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('22',plain,(
    ! [X26: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X30 @ X28 )
      | ( X30 = X29 )
      | ( X30 = X26 )
      | ( X28
       != ( k2_tarski @ X29 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('23',plain,(
    ! [X26: $i,X29: $i,X30: $i] :
      ( ( X30 = X26 )
      | ( X30 = X29 )
      | ~ ( r2_hidden @ X30 @ ( k2_tarski @ X29 @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A )
      | ( X0 = sk_B )
      | ( X0 = sk_C ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X15 != X14 )
      | ~ ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('26',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ~ ( zip_tseitin_0 @ X14 @ X16 @ X17 @ X14 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( sk_A = sk_C )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['27','28','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.emCT099Z3i
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:31:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.54/0.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.54/0.73  % Solved by: fo/fo7.sh
% 0.54/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.73  % done 800 iterations in 0.315s
% 0.54/0.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.54/0.73  % SZS output start Refutation
% 0.54/0.73  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.54/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.73  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.54/0.73  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.54/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.54/0.73  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.54/0.73  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.54/0.73  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.54/0.73  thf(sk_C_type, type, sk_C: $i).
% 0.54/0.73  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.54/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.73  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.54/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.73  thf(t25_zfmisc_1, conjecture,
% 0.54/0.73    (![A:$i,B:$i,C:$i]:
% 0.54/0.73     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.54/0.73          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 0.54/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.73    (~( ![A:$i,B:$i,C:$i]:
% 0.54/0.73        ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.54/0.73             ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ) )),
% 0.54/0.73    inference('cnf.neg', [status(esa)], [t25_zfmisc_1])).
% 0.54/0.73  thf('0', plain,
% 0.54/0.73      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf(l32_xboole_1, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.54/0.73  thf('1', plain,
% 0.54/0.73      (![X0 : $i, X2 : $i]:
% 0.54/0.73         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.54/0.73      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.54/0.73  thf('2', plain,
% 0.54/0.73      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.54/0.73         = (k1_xboole_0))),
% 0.54/0.73      inference('sup-', [status(thm)], ['0', '1'])).
% 0.54/0.73  thf(t98_xboole_1, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.54/0.73  thf('3', plain,
% 0.54/0.73      (![X12 : $i, X13 : $i]:
% 0.54/0.73         ((k2_xboole_0 @ X12 @ X13)
% 0.54/0.73           = (k5_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12)))),
% 0.54/0.73      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.54/0.73  thf('4', plain,
% 0.54/0.73      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_A))
% 0.54/0.73         = (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ k1_xboole_0))),
% 0.54/0.73      inference('sup+', [status(thm)], ['2', '3'])).
% 0.54/0.73  thf(t5_boole, axiom,
% 0.54/0.73    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.54/0.73  thf('5', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.54/0.73      inference('cnf', [status(esa)], [t5_boole])).
% 0.54/0.73  thf('6', plain,
% 0.54/0.73      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_A))
% 0.54/0.73         = (k2_tarski @ sk_B @ sk_C))),
% 0.54/0.73      inference('demod', [status(thm)], ['4', '5'])).
% 0.54/0.73  thf(t70_enumset1, axiom,
% 0.54/0.73    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.54/0.73  thf('7', plain,
% 0.54/0.73      (![X40 : $i, X41 : $i]:
% 0.54/0.73         ((k1_enumset1 @ X40 @ X40 @ X41) = (k2_tarski @ X40 @ X41))),
% 0.54/0.73      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.54/0.73  thf(t46_enumset1, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.73     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.54/0.73       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.54/0.73  thf('8', plain,
% 0.54/0.73      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.54/0.73         ((k2_enumset1 @ X35 @ X36 @ X37 @ X38)
% 0.54/0.73           = (k2_xboole_0 @ (k1_enumset1 @ X35 @ X36 @ X37) @ (k1_tarski @ X38)))),
% 0.54/0.73      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.54/0.73  thf('9', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.73         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.54/0.73           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.54/0.73      inference('sup+', [status(thm)], ['7', '8'])).
% 0.54/0.73  thf(t71_enumset1, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i]:
% 0.54/0.73     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.54/0.73  thf('10', plain,
% 0.54/0.73      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.54/0.73         ((k2_enumset1 @ X42 @ X42 @ X43 @ X44)
% 0.54/0.73           = (k1_enumset1 @ X42 @ X43 @ X44))),
% 0.54/0.73      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.54/0.73  thf(t98_enumset1, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i]:
% 0.54/0.73     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ A @ C @ B ) ))).
% 0.54/0.73  thf('11', plain,
% 0.54/0.73      (![X67 : $i, X68 : $i, X69 : $i]:
% 0.54/0.73         ((k1_enumset1 @ X67 @ X69 @ X68) = (k1_enumset1 @ X67 @ X68 @ X69))),
% 0.54/0.73      inference('cnf', [status(esa)], [t98_enumset1])).
% 0.54/0.73  thf('12', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.73         ((k1_enumset1 @ X2 @ X0 @ X1) = (k2_enumset1 @ X2 @ X2 @ X1 @ X0))),
% 0.54/0.73      inference('sup+', [status(thm)], ['10', '11'])).
% 0.54/0.73  thf('13', plain,
% 0.54/0.73      (![X67 : $i, X68 : $i, X69 : $i]:
% 0.54/0.73         ((k1_enumset1 @ X67 @ X69 @ X68) = (k1_enumset1 @ X67 @ X68 @ X69))),
% 0.54/0.73      inference('cnf', [status(esa)], [t98_enumset1])).
% 0.54/0.73  thf(t102_enumset1, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i]:
% 0.54/0.73     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ C @ B @ A ) ))).
% 0.54/0.73  thf('14', plain,
% 0.54/0.73      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.54/0.73         ((k1_enumset1 @ X34 @ X33 @ X32) = (k1_enumset1 @ X32 @ X33 @ X34))),
% 0.54/0.73      inference('cnf', [status(esa)], [t102_enumset1])).
% 0.54/0.73  thf('15', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.73         ((k1_enumset1 @ X1 @ X0 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.54/0.73      inference('sup+', [status(thm)], ['13', '14'])).
% 0.54/0.73  thf('16', plain,
% 0.54/0.73      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.54/0.73         ((k1_enumset1 @ X34 @ X33 @ X32) = (k1_enumset1 @ X32 @ X33 @ X34))),
% 0.54/0.73      inference('cnf', [status(esa)], [t102_enumset1])).
% 0.54/0.73  thf('17', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.73         ((k1_enumset1 @ X1 @ X2 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.54/0.73      inference('sup+', [status(thm)], ['15', '16'])).
% 0.54/0.73  thf('18', plain,
% 0.54/0.73      (((k1_enumset1 @ sk_A @ sk_B @ sk_C) = (k2_tarski @ sk_B @ sk_C))),
% 0.54/0.73      inference('demod', [status(thm)], ['6', '9', '12', '17'])).
% 0.54/0.73  thf(d1_enumset1, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.73     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.54/0.73       ( ![E:$i]:
% 0.54/0.73         ( ( r2_hidden @ E @ D ) <=>
% 0.54/0.73           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.54/0.73  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.54/0.73  thf(zf_stmt_2, axiom,
% 0.54/0.73    (![E:$i,C:$i,B:$i,A:$i]:
% 0.54/0.73     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.54/0.73       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.54/0.73  thf(zf_stmt_3, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.73     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.54/0.73       ( ![E:$i]:
% 0.54/0.73         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.54/0.73  thf('19', plain,
% 0.54/0.73      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.54/0.73         ((zip_tseitin_0 @ X19 @ X20 @ X21 @ X22)
% 0.54/0.73          | (r2_hidden @ X19 @ X23)
% 0.54/0.73          | ((X23) != (k1_enumset1 @ X22 @ X21 @ X20)))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.54/0.73  thf('20', plain,
% 0.54/0.73      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.54/0.73         ((r2_hidden @ X19 @ (k1_enumset1 @ X22 @ X21 @ X20))
% 0.54/0.73          | (zip_tseitin_0 @ X19 @ X20 @ X21 @ X22))),
% 0.54/0.73      inference('simplify', [status(thm)], ['19'])).
% 0.54/0.73  thf('21', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         ((r2_hidden @ X0 @ (k2_tarski @ sk_B @ sk_C))
% 0.54/0.73          | (zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A))),
% 0.54/0.73      inference('sup+', [status(thm)], ['18', '20'])).
% 0.54/0.73  thf(d2_tarski, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i]:
% 0.54/0.73     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.54/0.73       ( ![D:$i]:
% 0.54/0.73         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.54/0.73  thf('22', plain,
% 0.54/0.73      (![X26 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.54/0.73         (~ (r2_hidden @ X30 @ X28)
% 0.54/0.73          | ((X30) = (X29))
% 0.54/0.73          | ((X30) = (X26))
% 0.54/0.73          | ((X28) != (k2_tarski @ X29 @ X26)))),
% 0.54/0.73      inference('cnf', [status(esa)], [d2_tarski])).
% 0.54/0.73  thf('23', plain,
% 0.54/0.73      (![X26 : $i, X29 : $i, X30 : $i]:
% 0.54/0.73         (((X30) = (X26))
% 0.54/0.73          | ((X30) = (X29))
% 0.54/0.73          | ~ (r2_hidden @ X30 @ (k2_tarski @ X29 @ X26)))),
% 0.54/0.73      inference('simplify', [status(thm)], ['22'])).
% 0.54/0.73  thf('24', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         ((zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A)
% 0.54/0.73          | ((X0) = (sk_B))
% 0.54/0.73          | ((X0) = (sk_C)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['21', '23'])).
% 0.54/0.73  thf('25', plain,
% 0.54/0.73      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.54/0.73         (((X15) != (X14)) | ~ (zip_tseitin_0 @ X15 @ X16 @ X17 @ X14))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.54/0.73  thf('26', plain,
% 0.54/0.73      (![X14 : $i, X16 : $i, X17 : $i]:
% 0.54/0.73         ~ (zip_tseitin_0 @ X14 @ X16 @ X17 @ X14)),
% 0.54/0.73      inference('simplify', [status(thm)], ['25'])).
% 0.54/0.73  thf('27', plain, ((((sk_A) = (sk_C)) | ((sk_A) = (sk_B)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['24', '26'])).
% 0.54/0.73  thf('28', plain, (((sk_A) != (sk_B))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('29', plain, (((sk_A) != (sk_C))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('30', plain, ($false),
% 0.54/0.73      inference('simplify_reflect-', [status(thm)], ['27', '28', '29'])).
% 0.54/0.73  
% 0.54/0.73  % SZS output end Refutation
% 0.54/0.73  
% 0.54/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
