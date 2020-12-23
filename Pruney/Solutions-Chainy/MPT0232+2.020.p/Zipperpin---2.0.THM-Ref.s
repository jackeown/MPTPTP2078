%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.i65jAvSfjN

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:35 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 413 expanded)
%              Number of leaves         :   22 ( 116 expanded)
%              Depth                    :   19
%              Number of atoms          :  623 (4380 expanded)
%              Number of equality atoms :   68 ( 462 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t27_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
     => ( ( k2_tarski @ A @ B )
        = ( k1_tarski @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
       => ( ( k2_tarski @ A @ B )
          = ( k1_tarski @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_zfmisc_1])).

thf('0',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k1_tarski @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_enumset1 @ X26 @ X26 @ X27 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

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

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 )
      | ( r2_hidden @ X13 @ X17 )
      | ( X17
       != ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

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
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ~ ( zip_tseitin_0 @ X8 @ X10 @ X11 @ X8 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['8'])).

thf('10',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('12',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C_1 ) )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('14',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ sk_A @ sk_B )
        = ( k3_xboole_0 @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('17',plain,(
    ! [X20: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X23 @ X22 )
      | ( X23 = X20 )
      | ( X22
       != ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('18',plain,(
    ! [X20: $i,X23: $i] :
      ( ( X23 = X20 )
      | ~ ( r2_hidden @ X23 @ ( k1_tarski @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ sk_A @ sk_B )
        = ( k3_xboole_0 @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) )
      | ( ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_A @ sk_B ) @ X0 )
        = sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['8'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = ( k3_xboole_0 @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = ( k3_xboole_0 @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ sk_A @ sk_B )
        = ( k3_xboole_0 @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) )
      | ( r2_hidden @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X20: $i,X24: $i] :
      ( ( X24
        = ( k1_tarski @ X20 ) )
      | ( ( sk_C @ X24 @ X20 )
        = X20 )
      | ( r2_hidden @ ( sk_C @ X24 @ X20 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( k2_tarski @ sk_A @ sk_B ) @ X0 )
        = X0 )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X20: $i,X23: $i] :
      ( ( X23 = X20 )
      | ~ ( r2_hidden @ X23 @ ( k1_tarski @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ sk_A @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k2_tarski @ sk_A @ sk_B ) @ X0 )
        = X0 )
      | ( ( sk_C @ ( k2_tarski @ sk_A @ sk_B ) @ X0 )
        = sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 != X0 )
      | ( ( sk_C @ ( k2_tarski @ sk_A @ sk_B ) @ X0 )
        = X0 )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['27'])).

thf('29',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C_1 ) )
    | ( ( sk_C @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = sk_C_1 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k1_tarski @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( sk_C @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    = sk_C_1 ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X20: $i,X24: $i] :
      ( ( X24
        = ( k1_tarski @ X20 ) )
      | ( ( sk_C @ X24 @ X20 )
       != X20 )
      | ~ ( r2_hidden @ ( sk_C @ X24 @ X20 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('33',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) )
    | ( ( sk_C @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != sk_C_1 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_C @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    = sk_C_1 ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf('35',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) )
    | ( sk_C_1 != sk_C_1 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k1_tarski @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ~ ( r2_hidden @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ sk_A @ sk_B )
      = ( k3_xboole_0 @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['22','38'])).

thf('40',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('41',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ X0 ) ),
    inference('sup-',[status(thm)],['7','42'])).

thf('44',plain,(
    ! [X20: $i,X23: $i] :
      ( ( X23 = X20 )
      | ~ ( r2_hidden @ X23 @ ( k1_tarski @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('45',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('46',plain,(
    ! [X25: $i] :
      ( ( k2_tarski @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('47',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('48',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('49',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('50',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','45','46','47','48','49'])).

thf('51',plain,(
    $false ),
    inference(simplify,[status(thm)],['50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.i65jAvSfjN
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:28:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.62  % Solved by: fo/fo7.sh
% 0.39/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.62  % done 286 iterations in 0.164s
% 0.39/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.62  % SZS output start Refutation
% 0.39/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.62  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.39/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.39/0.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.39/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.39/0.62  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.39/0.62  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.39/0.62  thf(t27_zfmisc_1, conjecture,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.39/0.62       ( ( k2_tarski @ A @ B ) = ( k1_tarski @ C ) ) ))).
% 0.39/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.62    (~( ![A:$i,B:$i,C:$i]:
% 0.39/0.62        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.39/0.62          ( ( k2_tarski @ A @ B ) = ( k1_tarski @ C ) ) ) )),
% 0.39/0.62    inference('cnf.neg', [status(esa)], [t27_zfmisc_1])).
% 0.39/0.62  thf('0', plain, (((k2_tarski @ sk_A @ sk_B) != (k1_tarski @ sk_C_1))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(t70_enumset1, axiom,
% 0.39/0.62    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.39/0.62  thf('1', plain,
% 0.39/0.62      (![X26 : $i, X27 : $i]:
% 0.39/0.62         ((k1_enumset1 @ X26 @ X26 @ X27) = (k2_tarski @ X26 @ X27))),
% 0.39/0.62      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.39/0.62  thf(d1_enumset1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.62     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.39/0.62       ( ![E:$i]:
% 0.39/0.62         ( ( r2_hidden @ E @ D ) <=>
% 0.39/0.62           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.39/0.62  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.39/0.62  thf(zf_stmt_2, axiom,
% 0.39/0.62    (![E:$i,C:$i,B:$i,A:$i]:
% 0.39/0.62     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.39/0.62       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.39/0.62  thf(zf_stmt_3, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.62     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.39/0.62       ( ![E:$i]:
% 0.39/0.62         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.39/0.62  thf('2', plain,
% 0.39/0.62      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.39/0.62         ((zip_tseitin_0 @ X13 @ X14 @ X15 @ X16)
% 0.39/0.62          | (r2_hidden @ X13 @ X17)
% 0.39/0.62          | ((X17) != (k1_enumset1 @ X16 @ X15 @ X14)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.62  thf('3', plain,
% 0.39/0.62      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.39/0.62         ((r2_hidden @ X13 @ (k1_enumset1 @ X16 @ X15 @ X14))
% 0.39/0.62          | (zip_tseitin_0 @ X13 @ X14 @ X15 @ X16))),
% 0.39/0.62      inference('simplify', [status(thm)], ['2'])).
% 0.39/0.62  thf('4', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.62         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.39/0.62          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.39/0.62      inference('sup+', [status(thm)], ['1', '3'])).
% 0.39/0.62  thf('5', plain,
% 0.39/0.62      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.39/0.62         (((X9) != (X8)) | ~ (zip_tseitin_0 @ X9 @ X10 @ X11 @ X8))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.39/0.62  thf('6', plain,
% 0.39/0.62      (![X8 : $i, X10 : $i, X11 : $i]: ~ (zip_tseitin_0 @ X8 @ X10 @ X11 @ X8)),
% 0.39/0.62      inference('simplify', [status(thm)], ['5'])).
% 0.39/0.62  thf('7', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.39/0.62      inference('sup-', [status(thm)], ['4', '6'])).
% 0.39/0.62  thf(d4_xboole_0, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.39/0.62       ( ![D:$i]:
% 0.39/0.62         ( ( r2_hidden @ D @ C ) <=>
% 0.39/0.62           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.39/0.62  thf('8', plain,
% 0.39/0.62      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.39/0.62         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.39/0.62          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.39/0.62          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.39/0.62      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.39/0.62  thf('9', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.39/0.62          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.39/0.62      inference('eq_fact', [status(thm)], ['8'])).
% 0.39/0.62  thf('10', plain,
% 0.39/0.62      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C_1))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(t28_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.39/0.62  thf('11', plain,
% 0.39/0.62      (![X6 : $i, X7 : $i]:
% 0.39/0.62         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.39/0.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.39/0.62  thf('12', plain,
% 0.39/0.62      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C_1))
% 0.39/0.62         = (k2_tarski @ sk_A @ sk_B))),
% 0.39/0.62      inference('sup-', [status(thm)], ['10', '11'])).
% 0.39/0.62  thf('13', plain,
% 0.39/0.62      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.39/0.62         (~ (r2_hidden @ X4 @ X3)
% 0.39/0.62          | (r2_hidden @ X4 @ X2)
% 0.39/0.62          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.39/0.62      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.39/0.62  thf('14', plain,
% 0.39/0.62      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.39/0.62         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['13'])).
% 0.39/0.62  thf('15', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 0.39/0.62          | (r2_hidden @ X0 @ (k1_tarski @ sk_C_1)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['12', '14'])).
% 0.39/0.62  thf('16', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((k2_tarski @ sk_A @ sk_B)
% 0.39/0.62            = (k3_xboole_0 @ X0 @ (k2_tarski @ sk_A @ sk_B)))
% 0.39/0.62          | (r2_hidden @ 
% 0.39/0.62             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_A @ sk_B) @ X0) @ 
% 0.39/0.62             (k1_tarski @ sk_C_1)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['9', '15'])).
% 0.39/0.62  thf(d1_tarski, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.39/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.39/0.62  thf('17', plain,
% 0.39/0.62      (![X20 : $i, X22 : $i, X23 : $i]:
% 0.39/0.62         (~ (r2_hidden @ X23 @ X22)
% 0.39/0.62          | ((X23) = (X20))
% 0.39/0.62          | ((X22) != (k1_tarski @ X20)))),
% 0.39/0.62      inference('cnf', [status(esa)], [d1_tarski])).
% 0.39/0.62  thf('18', plain,
% 0.39/0.62      (![X20 : $i, X23 : $i]:
% 0.39/0.62         (((X23) = (X20)) | ~ (r2_hidden @ X23 @ (k1_tarski @ X20)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['17'])).
% 0.39/0.62  thf('19', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((k2_tarski @ sk_A @ sk_B)
% 0.39/0.62            = (k3_xboole_0 @ X0 @ (k2_tarski @ sk_A @ sk_B)))
% 0.39/0.62          | ((sk_D @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_A @ sk_B) @ X0)
% 0.39/0.62              = (sk_C_1)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['16', '18'])).
% 0.39/0.62  thf('20', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.39/0.62          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.39/0.62      inference('eq_fact', [status(thm)], ['8'])).
% 0.39/0.62  thf('21', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((r2_hidden @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.39/0.62          | ((k2_tarski @ sk_A @ sk_B)
% 0.39/0.62              = (k3_xboole_0 @ X0 @ (k2_tarski @ sk_A @ sk_B)))
% 0.39/0.62          | ((k2_tarski @ sk_A @ sk_B)
% 0.39/0.62              = (k3_xboole_0 @ X0 @ (k2_tarski @ sk_A @ sk_B))))),
% 0.39/0.62      inference('sup+', [status(thm)], ['19', '20'])).
% 0.39/0.62  thf('22', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((k2_tarski @ sk_A @ sk_B)
% 0.39/0.62            = (k3_xboole_0 @ X0 @ (k2_tarski @ sk_A @ sk_B)))
% 0.39/0.62          | (r2_hidden @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['21'])).
% 0.39/0.62  thf('23', plain,
% 0.39/0.62      (![X20 : $i, X24 : $i]:
% 0.39/0.62         (((X24) = (k1_tarski @ X20))
% 0.39/0.62          | ((sk_C @ X24 @ X20) = (X20))
% 0.39/0.62          | (r2_hidden @ (sk_C @ X24 @ X20) @ X24))),
% 0.39/0.62      inference('cnf', [status(esa)], [d1_tarski])).
% 0.39/0.62  thf('24', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 0.39/0.62          | (r2_hidden @ X0 @ (k1_tarski @ sk_C_1)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['12', '14'])).
% 0.39/0.62  thf('25', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((sk_C @ (k2_tarski @ sk_A @ sk_B) @ X0) = (X0))
% 0.39/0.62          | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ X0))
% 0.39/0.62          | (r2_hidden @ (sk_C @ (k2_tarski @ sk_A @ sk_B) @ X0) @ 
% 0.39/0.62             (k1_tarski @ sk_C_1)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['23', '24'])).
% 0.39/0.62  thf('26', plain,
% 0.39/0.62      (![X20 : $i, X23 : $i]:
% 0.39/0.62         (((X23) = (X20)) | ~ (r2_hidden @ X23 @ (k1_tarski @ X20)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['17'])).
% 0.39/0.62  thf('27', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ X0))
% 0.39/0.62          | ((sk_C @ (k2_tarski @ sk_A @ sk_B) @ X0) = (X0))
% 0.39/0.62          | ((sk_C @ (k2_tarski @ sk_A @ sk_B) @ X0) = (sk_C_1)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['25', '26'])).
% 0.39/0.62  thf('28', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((sk_C_1) != (X0))
% 0.39/0.62          | ((sk_C @ (k2_tarski @ sk_A @ sk_B) @ X0) = (X0))
% 0.39/0.62          | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ X0)))),
% 0.39/0.62      inference('eq_fact', [status(thm)], ['27'])).
% 0.39/0.62  thf('29', plain,
% 0.39/0.62      ((((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C_1))
% 0.39/0.62        | ((sk_C @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (sk_C_1)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['28'])).
% 0.39/0.62  thf('30', plain, (((k2_tarski @ sk_A @ sk_B) != (k1_tarski @ sk_C_1))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('31', plain, (((sk_C @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (sk_C_1))),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.39/0.62  thf('32', plain,
% 0.39/0.62      (![X20 : $i, X24 : $i]:
% 0.39/0.62         (((X24) = (k1_tarski @ X20))
% 0.39/0.62          | ((sk_C @ X24 @ X20) != (X20))
% 0.39/0.62          | ~ (r2_hidden @ (sk_C @ X24 @ X20) @ X24))),
% 0.39/0.62      inference('cnf', [status(esa)], [d1_tarski])).
% 0.39/0.62  thf('33', plain,
% 0.39/0.62      ((~ (r2_hidden @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.39/0.62        | ((sk_C @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) != (sk_C_1))
% 0.39/0.62        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C_1)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['31', '32'])).
% 0.39/0.62  thf('34', plain, (((sk_C @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (sk_C_1))),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.39/0.62  thf('35', plain,
% 0.39/0.62      ((~ (r2_hidden @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.39/0.62        | ((sk_C_1) != (sk_C_1))
% 0.39/0.62        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C_1)))),
% 0.39/0.62      inference('demod', [status(thm)], ['33', '34'])).
% 0.39/0.62  thf('36', plain,
% 0.39/0.62      ((((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C_1))
% 0.39/0.62        | ~ (r2_hidden @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['35'])).
% 0.39/0.62  thf('37', plain, (((k2_tarski @ sk_A @ sk_B) != (k1_tarski @ sk_C_1))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('38', plain, (~ (r2_hidden @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B))),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['36', '37'])).
% 0.39/0.62  thf('39', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((k2_tarski @ sk_A @ sk_B)
% 0.39/0.62           = (k3_xboole_0 @ X0 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.39/0.62      inference('clc', [status(thm)], ['22', '38'])).
% 0.39/0.62  thf('40', plain,
% 0.39/0.62      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.39/0.62         (~ (r2_hidden @ X4 @ X3)
% 0.39/0.62          | (r2_hidden @ X4 @ X1)
% 0.39/0.62          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.39/0.62      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.39/0.62  thf('41', plain,
% 0.39/0.62      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.39/0.62         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['40'])).
% 0.39/0.62  thf('42', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (~ (r2_hidden @ X1 @ (k2_tarski @ sk_A @ sk_B))
% 0.39/0.62          | (r2_hidden @ X1 @ X0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['39', '41'])).
% 0.39/0.62  thf('43', plain, (![X0 : $i]: (r2_hidden @ sk_A @ X0)),
% 0.39/0.62      inference('sup-', [status(thm)], ['7', '42'])).
% 0.39/0.62  thf('44', plain,
% 0.39/0.62      (![X20 : $i, X23 : $i]:
% 0.39/0.62         (((X23) = (X20)) | ~ (r2_hidden @ X23 @ (k1_tarski @ X20)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['17'])).
% 0.39/0.62  thf('45', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['43', '44'])).
% 0.39/0.62  thf(t69_enumset1, axiom,
% 0.39/0.62    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.39/0.62  thf('46', plain,
% 0.39/0.62      (![X25 : $i]: ((k2_tarski @ X25 @ X25) = (k1_tarski @ X25))),
% 0.39/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.39/0.62  thf('47', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['43', '44'])).
% 0.39/0.62  thf('48', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['43', '44'])).
% 0.39/0.62  thf('49', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['43', '44'])).
% 0.39/0.62  thf('50', plain, (((sk_A) != (sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['0', '45', '46', '47', '48', '49'])).
% 0.39/0.62  thf('51', plain, ($false), inference('simplify', [status(thm)], ['50'])).
% 0.39/0.62  
% 0.39/0.62  % SZS output end Refutation
% 0.39/0.62  
% 0.49/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
