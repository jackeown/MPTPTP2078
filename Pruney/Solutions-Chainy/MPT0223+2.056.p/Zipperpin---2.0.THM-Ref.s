%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dhkGDxklEx

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:38 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 134 expanded)
%              Number of leaves         :   19 (  45 expanded)
%              Depth                    :   20
%              Number of atoms          :  626 (1379 expanded)
%              Number of equality atoms :   55 ( 124 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( X9 = X10 )
      | ( X9 = X11 )
      | ( X9 = X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X21 @ X21 @ X22 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 )
      | ( r2_hidden @ X13 @ X17 )
      | ( X17
       != ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('3',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X13 @ ( k1_enumset1 @ X16 @ X15 @ X14 ) )
      | ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X9 != X8 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ~ ( zip_tseitin_0 @ X8 @ X10 @ X11 @ X8 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('8',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('9',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( X9 = X10 )
      | ( X9 = X11 )
      | ( X9 = X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('10',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['10'])).

thf('12',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('13',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X21 @ X21 @ X22 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('14',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X17 )
      | ~ ( zip_tseitin_0 @ X18 @ X14 @ X15 @ X16 )
      | ( X17
       != ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('15',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ~ ( zip_tseitin_0 @ X18 @ X14 @ X15 @ X16 )
      | ~ ( r2_hidden @ X18 @ ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ~ ( zip_tseitin_0 @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('22',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['20','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('28',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf(t18_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t18_zfmisc_1])).

thf('36',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('37',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('38',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','31'])).

thf('43',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('45',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['0','45'])).

thf('47',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('49',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['47','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dhkGDxklEx
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:53:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.36/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.55  % Solved by: fo/fo7.sh
% 0.36/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.55  % done 88 iterations in 0.083s
% 0.36/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.55  % SZS output start Refutation
% 0.36/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.55  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.36/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.55  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.36/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.55  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.36/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.55  thf(d1_enumset1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.55     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.36/0.55       ( ![E:$i]:
% 0.36/0.55         ( ( r2_hidden @ E @ D ) <=>
% 0.36/0.55           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.36/0.55  thf(zf_stmt_0, axiom,
% 0.36/0.55    (![E:$i,C:$i,B:$i,A:$i]:
% 0.36/0.55     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.36/0.55       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.36/0.55  thf('0', plain,
% 0.36/0.55      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.36/0.55         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 0.36/0.55          | ((X9) = (X10))
% 0.36/0.55          | ((X9) = (X11))
% 0.36/0.55          | ((X9) = (X12)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(t70_enumset1, axiom,
% 0.36/0.55    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.36/0.55  thf('1', plain,
% 0.36/0.55      (![X21 : $i, X22 : $i]:
% 0.36/0.55         ((k1_enumset1 @ X21 @ X21 @ X22) = (k2_tarski @ X21 @ X22))),
% 0.36/0.55      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.36/0.55  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.36/0.55  thf(zf_stmt_2, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.55     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.36/0.55       ( ![E:$i]:
% 0.36/0.55         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.36/0.55  thf('2', plain,
% 0.36/0.55      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.36/0.55         ((zip_tseitin_0 @ X13 @ X14 @ X15 @ X16)
% 0.36/0.55          | (r2_hidden @ X13 @ X17)
% 0.36/0.55          | ((X17) != (k1_enumset1 @ X16 @ X15 @ X14)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.36/0.55  thf('3', plain,
% 0.36/0.55      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.36/0.55         ((r2_hidden @ X13 @ (k1_enumset1 @ X16 @ X15 @ X14))
% 0.36/0.55          | (zip_tseitin_0 @ X13 @ X14 @ X15 @ X16))),
% 0.36/0.55      inference('simplify', [status(thm)], ['2'])).
% 0.36/0.55  thf('4', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.55         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.36/0.55          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.36/0.55      inference('sup+', [status(thm)], ['1', '3'])).
% 0.36/0.55  thf('5', plain,
% 0.36/0.55      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.36/0.55         (((X9) != (X8)) | ~ (zip_tseitin_0 @ X9 @ X10 @ X11 @ X8))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('6', plain,
% 0.36/0.55      (![X8 : $i, X10 : $i, X11 : $i]: ~ (zip_tseitin_0 @ X8 @ X10 @ X11 @ X8)),
% 0.36/0.55      inference('simplify', [status(thm)], ['5'])).
% 0.36/0.55  thf('7', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.36/0.55      inference('sup-', [status(thm)], ['4', '6'])).
% 0.36/0.55  thf(t69_enumset1, axiom,
% 0.36/0.55    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.36/0.55  thf('8', plain, (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 0.36/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.55  thf('9', plain,
% 0.36/0.55      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.36/0.55         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 0.36/0.55          | ((X9) = (X10))
% 0.36/0.55          | ((X9) = (X11))
% 0.36/0.55          | ((X9) = (X12)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(d5_xboole_0, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.36/0.55       ( ![D:$i]:
% 0.36/0.55         ( ( r2_hidden @ D @ C ) <=>
% 0.36/0.55           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.36/0.55  thf('10', plain,
% 0.36/0.55      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.36/0.55         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.36/0.55          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.36/0.55          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.36/0.55      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.36/0.55  thf('11', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.36/0.55          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.36/0.55      inference('eq_fact', [status(thm)], ['10'])).
% 0.36/0.55  thf('12', plain,
% 0.36/0.55      (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 0.36/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.55  thf('13', plain,
% 0.36/0.55      (![X21 : $i, X22 : $i]:
% 0.36/0.55         ((k1_enumset1 @ X21 @ X21 @ X22) = (k2_tarski @ X21 @ X22))),
% 0.36/0.55      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.36/0.55  thf('14', plain,
% 0.36/0.55      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X18 @ X17)
% 0.36/0.55          | ~ (zip_tseitin_0 @ X18 @ X14 @ X15 @ X16)
% 0.36/0.55          | ((X17) != (k1_enumset1 @ X16 @ X15 @ X14)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.36/0.55  thf('15', plain,
% 0.36/0.55      (![X14 : $i, X15 : $i, X16 : $i, X18 : $i]:
% 0.36/0.55         (~ (zip_tseitin_0 @ X18 @ X14 @ X15 @ X16)
% 0.36/0.55          | ~ (r2_hidden @ X18 @ (k1_enumset1 @ X16 @ X15 @ X14)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['14'])).
% 0.36/0.55  thf('16', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.36/0.55          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.36/0.55      inference('sup-', [status(thm)], ['13', '15'])).
% 0.36/0.55  thf('17', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.36/0.55          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['12', '16'])).
% 0.36/0.55  thf('18', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.36/0.55          | ~ (zip_tseitin_0 @ 
% 0.36/0.55               (sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) @ X0 @ X0 @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['11', '17'])).
% 0.36/0.55  thf('19', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (((sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.36/0.55          | ((sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.36/0.55          | ((sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.36/0.55          | ((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['9', '18'])).
% 0.36/0.55  thf('20', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.36/0.55          | ((sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['19'])).
% 0.36/0.55  thf('21', plain,
% 0.36/0.55      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.36/0.55         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.36/0.55          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.36/0.55          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.36/0.55      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.36/0.55  thf('22', plain,
% 0.36/0.55      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.36/0.55         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.36/0.55          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.36/0.55          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.36/0.55      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.36/0.55  thf('23', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.36/0.55          | ((X1) = (k4_xboole_0 @ X0 @ X0))
% 0.36/0.55          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.36/0.55          | ((X1) = (k4_xboole_0 @ X0 @ X0)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.36/0.55  thf('24', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 0.36/0.55          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 0.36/0.55      inference('simplify', [status(thm)], ['23'])).
% 0.36/0.55  thf('25', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.36/0.55          | ((k1_tarski @ X0)
% 0.36/0.55              = (k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))
% 0.36/0.55          | ((k1_tarski @ X0)
% 0.36/0.55              = (k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))))),
% 0.36/0.55      inference('sup+', [status(thm)], ['20', '24'])).
% 0.36/0.55  thf('26', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (((k1_tarski @ X0)
% 0.36/0.55            = (k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))
% 0.36/0.55          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['25'])).
% 0.36/0.55  thf('27', plain,
% 0.36/0.55      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X4 @ X3)
% 0.36/0.55          | ~ (r2_hidden @ X4 @ X2)
% 0.36/0.55          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.36/0.55      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.36/0.55  thf('28', plain,
% 0.36/0.55      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X4 @ X2)
% 0.36/0.55          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['27'])).
% 0.36/0.55  thf('29', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.36/0.55          | (r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.36/0.55          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['26', '28'])).
% 0.36/0.55  thf('30', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.36/0.55          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['29'])).
% 0.36/0.55  thf('31', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0))
% 0.36/0.55          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['8', '30'])).
% 0.36/0.55  thf('32', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['7', '31'])).
% 0.36/0.55  thf('33', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X0 @ X1)
% 0.36/0.55          | (r2_hidden @ X0 @ X2)
% 0.36/0.55          | (r2_hidden @ X0 @ X3)
% 0.36/0.55          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.36/0.55      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.36/0.55  thf('34', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.55         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.36/0.55          | (r2_hidden @ X0 @ X2)
% 0.36/0.55          | ~ (r2_hidden @ X0 @ X1))),
% 0.36/0.55      inference('simplify', [status(thm)], ['33'])).
% 0.36/0.55  thf('35', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         ((r2_hidden @ X0 @ X1)
% 0.36/0.55          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['32', '34'])).
% 0.36/0.55  thf(t18_zfmisc_1, conjecture,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.36/0.55         ( k1_tarski @ A ) ) =>
% 0.36/0.55       ( ( A ) = ( B ) ) ))).
% 0.36/0.55  thf(zf_stmt_3, negated_conjecture,
% 0.36/0.55    (~( ![A:$i,B:$i]:
% 0.36/0.55        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.36/0.55            ( k1_tarski @ A ) ) =>
% 0.36/0.55          ( ( A ) = ( B ) ) ) )),
% 0.36/0.55    inference('cnf.neg', [status(esa)], [t18_zfmisc_1])).
% 0.36/0.55  thf('36', plain,
% 0.36/0.55      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.36/0.55         = (k1_tarski @ sk_A))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.36/0.55  thf(t48_xboole_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.36/0.55  thf('37', plain,
% 0.36/0.55      (![X6 : $i, X7 : $i]:
% 0.36/0.55         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.36/0.55           = (k3_xboole_0 @ X6 @ X7))),
% 0.36/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.36/0.55  thf('38', plain,
% 0.36/0.55      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X4 @ X2)
% 0.36/0.55          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['27'])).
% 0.36/0.55  thf('39', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.36/0.55          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['37', '38'])).
% 0.36/0.55  thf('40', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.36/0.55          | ~ (r2_hidden @ X0 @ 
% 0.36/0.55               (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))))),
% 0.36/0.55      inference('sup-', [status(thm)], ['36', '39'])).
% 0.36/0.55  thf('41', plain,
% 0.36/0.55      (((r2_hidden @ sk_A @ (k1_tarski @ sk_B))
% 0.36/0.55        | ~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['35', '40'])).
% 0.36/0.55  thf('42', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['7', '31'])).
% 0.36/0.55  thf('43', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.36/0.55      inference('demod', [status(thm)], ['41', '42'])).
% 0.36/0.55  thf('44', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.36/0.55          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['12', '16'])).
% 0.36/0.55  thf('45', plain, (~ (zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B)),
% 0.36/0.55      inference('sup-', [status(thm)], ['43', '44'])).
% 0.36/0.55  thf('46', plain,
% 0.36/0.55      ((((sk_A) = (sk_B)) | ((sk_A) = (sk_B)) | ((sk_A) = (sk_B)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['0', '45'])).
% 0.36/0.55  thf('47', plain, (((sk_A) = (sk_B))),
% 0.36/0.55      inference('simplify', [status(thm)], ['46'])).
% 0.36/0.55  thf('48', plain, (((sk_A) != (sk_B))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.36/0.55  thf('49', plain, ($false),
% 0.36/0.55      inference('simplify_reflect-', [status(thm)], ['47', '48'])).
% 0.36/0.55  
% 0.36/0.55  % SZS output end Refutation
% 0.36/0.55  
% 0.36/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
