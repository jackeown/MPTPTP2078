%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yp7nttDjr6

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:47 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   71 (  80 expanded)
%              Number of leaves         :   29 (  36 expanded)
%              Depth                    :   14
%              Number of atoms          :  478 ( 579 expanded)
%              Number of equality atoms :   42 (  56 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('0',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 )
      | ( X15 = X16 )
      | ( X15 = X17 )
      | ( X15 = X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('2',plain,(
    ! [X54: $i,X55: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X54 ) @ X55 )
      | ( r2_hidden @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('3',plain,(
    ! [X56: $i,X58: $i,X59: $i] :
      ( ( r1_tarski @ X58 @ ( k2_tarski @ X56 @ X59 ) )
      | ( X58
       != ( k1_tarski @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('4',plain,(
    ! [X56: $i,X59: $i] :
      ( r1_tarski @ ( k1_tarski @ X56 ) @ ( k2_tarski @ X56 @ X59 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t28_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
        & ( A != C )
        & ( A != D ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
          & ( A != C )
          & ( A != D ) ) ),
    inference('cnf.neg',[status(esa)],[t28_zfmisc_1])).

thf('5',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B_1 ) @ ( k2_tarski @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('7',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ ( k2_tarski @ sk_C_1 @ sk_D ) )
    = ( k2_tarski @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_tarski @ sk_A @ sk_B_1 ) )
      | ( r1_tarski @ X0 @ ( k2_tarski @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('14',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('15',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k2_tarski @ sk_C_1 @ sk_D ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','16'])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k2_tarski @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','17'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_enumset1 @ X27 @ X27 @ X28 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X24 @ X23 )
      | ~ ( zip_tseitin_0 @ X24 @ X20 @ X21 @ X22 )
      | ( X23
       != ( k1_enumset1 @ X22 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('21',plain,(
    ! [X20: $i,X21: $i,X22: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X20 @ X21 @ X22 )
      | ~ ( r2_hidden @ X24 @ ( k1_enumset1 @ X22 @ X21 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_D @ sk_C_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,
    ( ( sk_A = sk_C_1 )
    | ( sk_A = sk_C_1 )
    | ( sk_A = sk_D )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','23'])).

thf('25',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_A ) )
    | ( sk_A = sk_D )
    | ( sk_A = sk_C_1 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('27',plain,(
    sk_A != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('28',plain,(
    v1_xboole_0 @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['25','26','27'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('29',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('30',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_enumset1 @ X27 @ X27 @ X28 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('31',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 )
      | ( r2_hidden @ X19 @ X23 )
      | ( X23
       != ( k1_enumset1 @ X22 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('32',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ X19 @ ( k1_enumset1 @ X22 @ X21 @ X20 ) )
      | ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X15 != X14 )
      | ~ ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ~ ( zip_tseitin_0 @ X14 @ X16 @ X17 @ X14 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','38'])).

thf('40',plain,(
    $false ),
    inference('sup-',[status(thm)],['28','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yp7nttDjr6
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:49:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.40/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.60  % Solved by: fo/fo7.sh
% 0.40/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.60  % done 357 iterations in 0.148s
% 0.40/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.60  % SZS output start Refutation
% 0.40/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.60  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.40/0.60  thf(sk_B_type, type, sk_B: $i > $i).
% 0.40/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.60  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.40/0.60  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.40/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.60  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.40/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.40/0.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.40/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.60  thf(sk_D_type, type, sk_D: $i).
% 0.40/0.60  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.40/0.60  thf(d1_enumset1, axiom,
% 0.40/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.60     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.40/0.60       ( ![E:$i]:
% 0.40/0.60         ( ( r2_hidden @ E @ D ) <=>
% 0.40/0.60           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.40/0.60  thf(zf_stmt_0, axiom,
% 0.40/0.60    (![E:$i,C:$i,B:$i,A:$i]:
% 0.40/0.60     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.40/0.60       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.40/0.60  thf('0', plain,
% 0.40/0.60      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.40/0.60         ((zip_tseitin_0 @ X15 @ X16 @ X17 @ X18)
% 0.40/0.60          | ((X15) = (X16))
% 0.40/0.60          | ((X15) = (X17))
% 0.40/0.60          | ((X15) = (X18)))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf(d1_xboole_0, axiom,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.40/0.60  thf('1', plain,
% 0.40/0.60      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.40/0.60      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.40/0.60  thf(l27_zfmisc_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.40/0.60  thf('2', plain,
% 0.40/0.60      (![X54 : $i, X55 : $i]:
% 0.40/0.60         ((r1_xboole_0 @ (k1_tarski @ X54) @ X55) | (r2_hidden @ X54 @ X55))),
% 0.40/0.60      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.40/0.60  thf(l45_zfmisc_1, axiom,
% 0.40/0.60    (![A:$i,B:$i,C:$i]:
% 0.40/0.60     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.40/0.60       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.40/0.60            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.40/0.60  thf('3', plain,
% 0.40/0.60      (![X56 : $i, X58 : $i, X59 : $i]:
% 0.40/0.60         ((r1_tarski @ X58 @ (k2_tarski @ X56 @ X59))
% 0.40/0.60          | ((X58) != (k1_tarski @ X56)))),
% 0.40/0.60      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.40/0.60  thf('4', plain,
% 0.40/0.60      (![X56 : $i, X59 : $i]:
% 0.40/0.60         (r1_tarski @ (k1_tarski @ X56) @ (k2_tarski @ X56 @ X59))),
% 0.40/0.60      inference('simplify', [status(thm)], ['3'])).
% 0.40/0.60  thf(t28_zfmisc_1, conjecture,
% 0.40/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.60     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.40/0.60          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 0.40/0.60  thf(zf_stmt_1, negated_conjecture,
% 0.40/0.60    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.60        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.40/0.60             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 0.40/0.60    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 0.40/0.60  thf('5', plain,
% 0.40/0.60      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B_1) @ (k2_tarski @ sk_C_1 @ sk_D))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.40/0.60  thf(t28_xboole_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.40/0.60  thf('6', plain,
% 0.40/0.60      (![X12 : $i, X13 : $i]:
% 0.40/0.60         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.40/0.60      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.40/0.60  thf('7', plain,
% 0.40/0.60      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ 
% 0.40/0.60         (k2_tarski @ sk_C_1 @ sk_D)) = (k2_tarski @ sk_A @ sk_B_1))),
% 0.40/0.60      inference('sup-', [status(thm)], ['5', '6'])).
% 0.40/0.60  thf(commutativity_k3_xboole_0, axiom,
% 0.40/0.60    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.40/0.60  thf('8', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.40/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.40/0.60  thf(t18_xboole_1, axiom,
% 0.40/0.60    (![A:$i,B:$i,C:$i]:
% 0.40/0.60     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 0.40/0.60  thf('9', plain,
% 0.40/0.60      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.40/0.60         ((r1_tarski @ X9 @ X10)
% 0.40/0.60          | ~ (r1_tarski @ X9 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.40/0.60      inference('cnf', [status(esa)], [t18_xboole_1])).
% 0.40/0.60  thf('10', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.60         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['8', '9'])).
% 0.40/0.60  thf('11', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (~ (r1_tarski @ X0 @ (k2_tarski @ sk_A @ sk_B_1))
% 0.40/0.60          | (r1_tarski @ X0 @ (k2_tarski @ sk_C_1 @ sk_D)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['7', '10'])).
% 0.40/0.60  thf('12', plain,
% 0.40/0.60      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D))),
% 0.40/0.60      inference('sup-', [status(thm)], ['4', '11'])).
% 0.40/0.60  thf('13', plain,
% 0.40/0.60      (![X12 : $i, X13 : $i]:
% 0.40/0.60         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.40/0.60      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.40/0.60  thf('14', plain,
% 0.40/0.60      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D))
% 0.40/0.60         = (k1_tarski @ sk_A))),
% 0.40/0.60      inference('sup-', [status(thm)], ['12', '13'])).
% 0.40/0.60  thf(t4_xboole_0, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.40/0.60            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.40/0.60       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.40/0.60            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.40/0.60  thf('15', plain,
% 0.40/0.60      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.40/0.60         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.40/0.60          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.40/0.60      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.40/0.60  thf('16', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.40/0.60          | ~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['14', '15'])).
% 0.40/0.60  thf('17', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         ((r2_hidden @ sk_A @ (k2_tarski @ sk_C_1 @ sk_D))
% 0.40/0.60          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['2', '16'])).
% 0.40/0.60  thf('18', plain,
% 0.40/0.60      (((v1_xboole_0 @ (k1_tarski @ sk_A))
% 0.40/0.60        | (r2_hidden @ sk_A @ (k2_tarski @ sk_C_1 @ sk_D)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['1', '17'])).
% 0.40/0.60  thf(t70_enumset1, axiom,
% 0.40/0.60    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.40/0.60  thf('19', plain,
% 0.40/0.60      (![X27 : $i, X28 : $i]:
% 0.40/0.60         ((k1_enumset1 @ X27 @ X27 @ X28) = (k2_tarski @ X27 @ X28))),
% 0.40/0.60      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.40/0.60  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.40/0.60  thf(zf_stmt_3, axiom,
% 0.40/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.60     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.40/0.60       ( ![E:$i]:
% 0.40/0.60         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.40/0.60  thf('20', plain,
% 0.40/0.60      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.40/0.60         (~ (r2_hidden @ X24 @ X23)
% 0.40/0.60          | ~ (zip_tseitin_0 @ X24 @ X20 @ X21 @ X22)
% 0.40/0.60          | ((X23) != (k1_enumset1 @ X22 @ X21 @ X20)))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.40/0.60  thf('21', plain,
% 0.40/0.60      (![X20 : $i, X21 : $i, X22 : $i, X24 : $i]:
% 0.40/0.60         (~ (zip_tseitin_0 @ X24 @ X20 @ X21 @ X22)
% 0.40/0.60          | ~ (r2_hidden @ X24 @ (k1_enumset1 @ X22 @ X21 @ X20)))),
% 0.40/0.60      inference('simplify', [status(thm)], ['20'])).
% 0.40/0.60  thf('22', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.60         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.40/0.60          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.40/0.60      inference('sup-', [status(thm)], ['19', '21'])).
% 0.40/0.60  thf('23', plain,
% 0.40/0.60      (((v1_xboole_0 @ (k1_tarski @ sk_A))
% 0.40/0.60        | ~ (zip_tseitin_0 @ sk_A @ sk_D @ sk_C_1 @ sk_C_1))),
% 0.40/0.60      inference('sup-', [status(thm)], ['18', '22'])).
% 0.40/0.60  thf('24', plain,
% 0.40/0.60      ((((sk_A) = (sk_C_1))
% 0.40/0.60        | ((sk_A) = (sk_C_1))
% 0.40/0.60        | ((sk_A) = (sk_D))
% 0.40/0.60        | (v1_xboole_0 @ (k1_tarski @ sk_A)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['0', '23'])).
% 0.40/0.60  thf('25', plain,
% 0.40/0.60      (((v1_xboole_0 @ (k1_tarski @ sk_A))
% 0.40/0.60        | ((sk_A) = (sk_D))
% 0.40/0.60        | ((sk_A) = (sk_C_1)))),
% 0.40/0.60      inference('simplify', [status(thm)], ['24'])).
% 0.40/0.60  thf('26', plain, (((sk_A) != (sk_C_1))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.40/0.60  thf('27', plain, (((sk_A) != (sk_D))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.40/0.60  thf('28', plain, ((v1_xboole_0 @ (k1_tarski @ sk_A))),
% 0.40/0.60      inference('simplify_reflect-', [status(thm)], ['25', '26', '27'])).
% 0.40/0.60  thf(t69_enumset1, axiom,
% 0.40/0.60    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.40/0.60  thf('29', plain,
% 0.40/0.60      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 0.40/0.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.40/0.60  thf('30', plain,
% 0.40/0.60      (![X27 : $i, X28 : $i]:
% 0.40/0.60         ((k1_enumset1 @ X27 @ X27 @ X28) = (k2_tarski @ X27 @ X28))),
% 0.40/0.60      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.40/0.60  thf('31', plain,
% 0.40/0.60      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.40/0.60         ((zip_tseitin_0 @ X19 @ X20 @ X21 @ X22)
% 0.40/0.60          | (r2_hidden @ X19 @ X23)
% 0.40/0.60          | ((X23) != (k1_enumset1 @ X22 @ X21 @ X20)))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.40/0.60  thf('32', plain,
% 0.40/0.60      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.40/0.60         ((r2_hidden @ X19 @ (k1_enumset1 @ X22 @ X21 @ X20))
% 0.40/0.60          | (zip_tseitin_0 @ X19 @ X20 @ X21 @ X22))),
% 0.40/0.60      inference('simplify', [status(thm)], ['31'])).
% 0.40/0.60  thf('33', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.60         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.40/0.60          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.40/0.60      inference('sup+', [status(thm)], ['30', '32'])).
% 0.40/0.60  thf('34', plain,
% 0.40/0.60      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.40/0.60         (((X15) != (X14)) | ~ (zip_tseitin_0 @ X15 @ X16 @ X17 @ X14))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('35', plain,
% 0.40/0.60      (![X14 : $i, X16 : $i, X17 : $i]:
% 0.40/0.60         ~ (zip_tseitin_0 @ X14 @ X16 @ X17 @ X14)),
% 0.40/0.60      inference('simplify', [status(thm)], ['34'])).
% 0.40/0.60  thf('36', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.40/0.60      inference('sup-', [status(thm)], ['33', '35'])).
% 0.40/0.60  thf('37', plain,
% 0.40/0.60      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.40/0.60      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.40/0.60  thf('38', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X1 @ X0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['36', '37'])).
% 0.40/0.60  thf('39', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['29', '38'])).
% 0.40/0.60  thf('40', plain, ($false), inference('sup-', [status(thm)], ['28', '39'])).
% 0.40/0.60  
% 0.40/0.60  % SZS output end Refutation
% 0.40/0.60  
% 0.40/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
