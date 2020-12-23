%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.62k4nGwX6h

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:33 EST 2020

% Result     : Theorem 0.97s
% Output     : Refutation 0.97s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 484 expanded)
%              Number of leaves         :   22 ( 137 expanded)
%              Depth                    :   19
%              Number of atoms          :  723 (5148 expanded)
%              Number of equality atoms :   74 ( 521 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X30: $i,X31: $i] :
      ( ( k1_enumset1 @ X30 @ X30 @ X31 )
      = ( k2_tarski @ X30 @ X31 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 )
      | ( r2_hidden @ X18 @ X22 )
      | ( X22
       != ( k1_enumset1 @ X21 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('3',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X18 @ ( k1_enumset1 @ X21 @ X20 @ X19 ) )
      | ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X14 != X13 )
      | ~ ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ~ ( zip_tseitin_0 @ X13 @ X15 @ X16 @ X13 ) ),
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
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C_1 ) )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('13',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) @ X1 )
      | ( X1
        = ( k3_xboole_0 @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) )
      | ( r2_hidden @ ( sk_D @ X1 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) @ ( k1_tarski @ sk_C_1 ) )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = ( k3_xboole_0 @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ sk_A @ sk_B )
        = ( k3_xboole_0 @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('19',plain,(
    ! [X25: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X28 @ X27 )
      | ( X28 = X25 )
      | ( X27
       != ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('20',plain,(
    ! [X25: $i,X28: $i] :
      ( ( X28 = X25 )
      | ~ ( r2_hidden @ X28 @ ( k1_tarski @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ sk_A @ sk_B )
        = ( k3_xboole_0 @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) )
      | ( ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_A @ sk_B ) @ X0 )
        = sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = ( k3_xboole_0 @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = ( k3_xboole_0 @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ sk_A @ sk_B )
        = ( k3_xboole_0 @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) )
      | ( r2_hidden @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X25: $i,X29: $i] :
      ( ( X29
        = ( k1_tarski @ X25 ) )
      | ( ( sk_C @ X29 @ X25 )
        = X25 )
      | ( r2_hidden @ ( sk_C @ X29 @ X25 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( k2_tarski @ sk_A @ sk_B ) @ X0 )
        = X0 )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X25: $i,X28: $i] :
      ( ( X28 = X25 )
      | ~ ( r2_hidden @ X28 @ ( k1_tarski @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ sk_A @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k2_tarski @ sk_A @ sk_B ) @ X0 )
        = X0 )
      | ( ( sk_C @ ( k2_tarski @ sk_A @ sk_B ) @ X0 )
        = sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 != X0 )
      | ( ( sk_C @ ( k2_tarski @ sk_A @ sk_B ) @ X0 )
        = X0 )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['30'])).

thf('32',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C_1 ) )
    | ( ( sk_C @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = sk_C_1 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k1_tarski @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( sk_C @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    = sk_C_1 ),
    inference('simplify_reflect-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X25: $i,X29: $i] :
      ( ( X29
        = ( k1_tarski @ X25 ) )
      | ( ( sk_C @ X29 @ X25 )
       != X25 )
      | ~ ( r2_hidden @ ( sk_C @ X29 @ X25 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('36',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) )
    | ( ( sk_C @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != sk_C_1 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_C @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    = sk_C_1 ),
    inference('simplify_reflect-',[status(thm)],['32','33'])).

thf('38',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) )
    | ( sk_C_1 != sk_C_1 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k1_tarski @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ~ ( r2_hidden @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ sk_A @ sk_B )
      = ( k3_xboole_0 @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['25','41'])).

thf('43',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('44',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ X0 ) ),
    inference('sup-',[status(thm)],['7','45'])).

thf(t76_enumset1,axiom,(
    ! [A: $i] :
      ( ( k1_enumset1 @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('47',plain,(
    ! [X48: $i] :
      ( ( k1_enumset1 @ X48 @ X48 @ X48 )
      = ( k1_tarski @ X48 ) ) ),
    inference(cnf,[status(esa)],[t76_enumset1])).

thf('48',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k1_enumset1 @ X30 @ X30 @ X31 )
      = ( k2_tarski @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('49',plain,(
    ! [X48: $i] :
      ( ( k2_tarski @ X48 @ X48 )
      = ( k1_tarski @ X48 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X25: $i,X28: $i] :
      ( ( X28 = X25 )
      | ~ ( r2_hidden @ X28 @ ( k1_tarski @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference('sup-',[status(thm)],['46','51'])).

thf('53',plain,(
    ! [X48: $i] :
      ( ( k2_tarski @ X48 @ X48 )
      = ( k1_tarski @ X48 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('54',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference('sup-',[status(thm)],['46','51'])).

thf('55',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference('sup-',[status(thm)],['46','51'])).

thf('56',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference('sup-',[status(thm)],['46','51'])).

thf('57',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','52','53','54','55','56'])).

thf('58',plain,(
    $false ),
    inference(simplify,[status(thm)],['57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.62k4nGwX6h
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:00:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.97/1.15  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.97/1.15  % Solved by: fo/fo7.sh
% 0.97/1.15  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.97/1.15  % done 742 iterations in 0.700s
% 0.97/1.15  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.97/1.15  % SZS output start Refutation
% 0.97/1.15  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.97/1.15  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.97/1.15  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.97/1.15  thf(sk_B_type, type, sk_B: $i).
% 0.97/1.15  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.97/1.15  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.97/1.15  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.97/1.15  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.97/1.15  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.97/1.15  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.97/1.15  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.97/1.15  thf(sk_A_type, type, sk_A: $i).
% 0.97/1.15  thf(t27_zfmisc_1, conjecture,
% 0.97/1.15    (![A:$i,B:$i,C:$i]:
% 0.97/1.15     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.97/1.15       ( ( k2_tarski @ A @ B ) = ( k1_tarski @ C ) ) ))).
% 0.97/1.15  thf(zf_stmt_0, negated_conjecture,
% 0.97/1.15    (~( ![A:$i,B:$i,C:$i]:
% 0.97/1.15        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.97/1.15          ( ( k2_tarski @ A @ B ) = ( k1_tarski @ C ) ) ) )),
% 0.97/1.15    inference('cnf.neg', [status(esa)], [t27_zfmisc_1])).
% 0.97/1.15  thf('0', plain, (((k2_tarski @ sk_A @ sk_B) != (k1_tarski @ sk_C_1))),
% 0.97/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.15  thf(t70_enumset1, axiom,
% 0.97/1.15    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.97/1.15  thf('1', plain,
% 0.97/1.15      (![X30 : $i, X31 : $i]:
% 0.97/1.15         ((k1_enumset1 @ X30 @ X30 @ X31) = (k2_tarski @ X30 @ X31))),
% 0.97/1.15      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.97/1.15  thf(d1_enumset1, axiom,
% 0.97/1.15    (![A:$i,B:$i,C:$i,D:$i]:
% 0.97/1.15     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.97/1.15       ( ![E:$i]:
% 0.97/1.15         ( ( r2_hidden @ E @ D ) <=>
% 0.97/1.15           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.97/1.15  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.97/1.15  thf(zf_stmt_2, axiom,
% 0.97/1.15    (![E:$i,C:$i,B:$i,A:$i]:
% 0.97/1.15     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.97/1.15       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.97/1.15  thf(zf_stmt_3, axiom,
% 0.97/1.15    (![A:$i,B:$i,C:$i,D:$i]:
% 0.97/1.15     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.97/1.15       ( ![E:$i]:
% 0.97/1.15         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.97/1.15  thf('2', plain,
% 0.97/1.15      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.97/1.15         ((zip_tseitin_0 @ X18 @ X19 @ X20 @ X21)
% 0.97/1.15          | (r2_hidden @ X18 @ X22)
% 0.97/1.15          | ((X22) != (k1_enumset1 @ X21 @ X20 @ X19)))),
% 0.97/1.15      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.97/1.15  thf('3', plain,
% 0.97/1.15      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.97/1.15         ((r2_hidden @ X18 @ (k1_enumset1 @ X21 @ X20 @ X19))
% 0.97/1.15          | (zip_tseitin_0 @ X18 @ X19 @ X20 @ X21))),
% 0.97/1.15      inference('simplify', [status(thm)], ['2'])).
% 0.97/1.15  thf('4', plain,
% 0.97/1.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.15         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.97/1.15          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.97/1.15      inference('sup+', [status(thm)], ['1', '3'])).
% 0.97/1.15  thf('5', plain,
% 0.97/1.15      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.97/1.15         (((X14) != (X13)) | ~ (zip_tseitin_0 @ X14 @ X15 @ X16 @ X13))),
% 0.97/1.15      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.97/1.15  thf('6', plain,
% 0.97/1.15      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.97/1.15         ~ (zip_tseitin_0 @ X13 @ X15 @ X16 @ X13)),
% 0.97/1.15      inference('simplify', [status(thm)], ['5'])).
% 0.97/1.15  thf('7', plain,
% 0.97/1.15      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.97/1.15      inference('sup-', [status(thm)], ['4', '6'])).
% 0.97/1.15  thf(d4_xboole_0, axiom,
% 0.97/1.15    (![A:$i,B:$i,C:$i]:
% 0.97/1.15     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.97/1.15       ( ![D:$i]:
% 0.97/1.15         ( ( r2_hidden @ D @ C ) <=>
% 0.97/1.15           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.97/1.15  thf('8', plain,
% 0.97/1.15      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.97/1.15         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.97/1.15          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.97/1.15          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.97/1.15      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.97/1.15  thf('9', plain,
% 0.97/1.15      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C_1))),
% 0.97/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.15  thf(t28_xboole_1, axiom,
% 0.97/1.15    (![A:$i,B:$i]:
% 0.97/1.15     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.97/1.15  thf('10', plain,
% 0.97/1.15      (![X9 : $i, X10 : $i]:
% 0.97/1.15         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.97/1.15      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.97/1.15  thf('11', plain,
% 0.97/1.15      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C_1))
% 0.97/1.15         = (k2_tarski @ sk_A @ sk_B))),
% 0.97/1.15      inference('sup-', [status(thm)], ['9', '10'])).
% 0.97/1.15  thf('12', plain,
% 0.97/1.15      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.97/1.15         (~ (r2_hidden @ X4 @ X3)
% 0.97/1.15          | (r2_hidden @ X4 @ X2)
% 0.97/1.15          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.97/1.15      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.97/1.15  thf('13', plain,
% 0.97/1.15      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.97/1.15         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.97/1.15      inference('simplify', [status(thm)], ['12'])).
% 0.97/1.15  thf('14', plain,
% 0.97/1.15      (![X0 : $i]:
% 0.97/1.15         (~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 0.97/1.15          | (r2_hidden @ X0 @ (k1_tarski @ sk_C_1)))),
% 0.97/1.15      inference('sup-', [status(thm)], ['11', '13'])).
% 0.97/1.15  thf('15', plain,
% 0.97/1.15      (![X0 : $i, X1 : $i]:
% 0.97/1.15         ((r2_hidden @ (sk_D @ X1 @ (k2_tarski @ sk_A @ sk_B) @ X0) @ X1)
% 0.97/1.15          | ((X1) = (k3_xboole_0 @ X0 @ (k2_tarski @ sk_A @ sk_B)))
% 0.97/1.15          | (r2_hidden @ (sk_D @ X1 @ (k2_tarski @ sk_A @ sk_B) @ X0) @ 
% 0.97/1.15             (k1_tarski @ sk_C_1)))),
% 0.97/1.15      inference('sup-', [status(thm)], ['8', '14'])).
% 0.97/1.15  thf('16', plain,
% 0.97/1.15      (![X0 : $i]:
% 0.97/1.15         (~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 0.97/1.15          | (r2_hidden @ X0 @ (k1_tarski @ sk_C_1)))),
% 0.97/1.15      inference('sup-', [status(thm)], ['11', '13'])).
% 0.97/1.15  thf('17', plain,
% 0.97/1.15      (![X0 : $i]:
% 0.97/1.15         ((r2_hidden @ 
% 0.97/1.15           (sk_D @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_A @ sk_B) @ X0) @ 
% 0.97/1.15           (k1_tarski @ sk_C_1))
% 0.97/1.15          | ((k2_tarski @ sk_A @ sk_B)
% 0.97/1.15              = (k3_xboole_0 @ X0 @ (k2_tarski @ sk_A @ sk_B)))
% 0.97/1.15          | (r2_hidden @ 
% 0.97/1.15             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_A @ sk_B) @ X0) @ 
% 0.97/1.15             (k1_tarski @ sk_C_1)))),
% 0.97/1.15      inference('sup-', [status(thm)], ['15', '16'])).
% 0.97/1.15  thf('18', plain,
% 0.97/1.15      (![X0 : $i]:
% 0.97/1.15         (((k2_tarski @ sk_A @ sk_B)
% 0.97/1.15            = (k3_xboole_0 @ X0 @ (k2_tarski @ sk_A @ sk_B)))
% 0.97/1.15          | (r2_hidden @ 
% 0.97/1.15             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_A @ sk_B) @ X0) @ 
% 0.97/1.15             (k1_tarski @ sk_C_1)))),
% 0.97/1.15      inference('simplify', [status(thm)], ['17'])).
% 0.97/1.15  thf(d1_tarski, axiom,
% 0.97/1.15    (![A:$i,B:$i]:
% 0.97/1.15     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.97/1.15       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.97/1.15  thf('19', plain,
% 0.97/1.15      (![X25 : $i, X27 : $i, X28 : $i]:
% 0.97/1.15         (~ (r2_hidden @ X28 @ X27)
% 0.97/1.15          | ((X28) = (X25))
% 0.97/1.15          | ((X27) != (k1_tarski @ X25)))),
% 0.97/1.15      inference('cnf', [status(esa)], [d1_tarski])).
% 0.97/1.15  thf('20', plain,
% 0.97/1.15      (![X25 : $i, X28 : $i]:
% 0.97/1.15         (((X28) = (X25)) | ~ (r2_hidden @ X28 @ (k1_tarski @ X25)))),
% 0.97/1.15      inference('simplify', [status(thm)], ['19'])).
% 0.97/1.15  thf('21', plain,
% 0.97/1.15      (![X0 : $i]:
% 0.97/1.15         (((k2_tarski @ sk_A @ sk_B)
% 0.97/1.15            = (k3_xboole_0 @ X0 @ (k2_tarski @ sk_A @ sk_B)))
% 0.97/1.15          | ((sk_D @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_A @ sk_B) @ X0)
% 0.97/1.15              = (sk_C_1)))),
% 0.97/1.15      inference('sup-', [status(thm)], ['18', '20'])).
% 0.97/1.15  thf('22', plain,
% 0.97/1.15      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.97/1.15         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.97/1.15          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.97/1.15          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.97/1.15      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.97/1.15  thf('23', plain,
% 0.97/1.15      (![X0 : $i, X1 : $i]:
% 0.97/1.15         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.97/1.15          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.97/1.15      inference('eq_fact', [status(thm)], ['22'])).
% 0.97/1.15  thf('24', plain,
% 0.97/1.15      (![X0 : $i]:
% 0.97/1.15         ((r2_hidden @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.97/1.15          | ((k2_tarski @ sk_A @ sk_B)
% 0.97/1.15              = (k3_xboole_0 @ X0 @ (k2_tarski @ sk_A @ sk_B)))
% 0.97/1.15          | ((k2_tarski @ sk_A @ sk_B)
% 0.97/1.15              = (k3_xboole_0 @ X0 @ (k2_tarski @ sk_A @ sk_B))))),
% 0.97/1.15      inference('sup+', [status(thm)], ['21', '23'])).
% 0.97/1.15  thf('25', plain,
% 0.97/1.15      (![X0 : $i]:
% 0.97/1.15         (((k2_tarski @ sk_A @ sk_B)
% 0.97/1.15            = (k3_xboole_0 @ X0 @ (k2_tarski @ sk_A @ sk_B)))
% 0.97/1.15          | (r2_hidden @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.97/1.15      inference('simplify', [status(thm)], ['24'])).
% 0.97/1.15  thf('26', plain,
% 0.97/1.15      (![X25 : $i, X29 : $i]:
% 0.97/1.15         (((X29) = (k1_tarski @ X25))
% 0.97/1.15          | ((sk_C @ X29 @ X25) = (X25))
% 0.97/1.15          | (r2_hidden @ (sk_C @ X29 @ X25) @ X29))),
% 0.97/1.15      inference('cnf', [status(esa)], [d1_tarski])).
% 0.97/1.15  thf('27', plain,
% 0.97/1.15      (![X0 : $i]:
% 0.97/1.15         (~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 0.97/1.15          | (r2_hidden @ X0 @ (k1_tarski @ sk_C_1)))),
% 0.97/1.15      inference('sup-', [status(thm)], ['11', '13'])).
% 0.97/1.15  thf('28', plain,
% 0.97/1.15      (![X0 : $i]:
% 0.97/1.15         (((sk_C @ (k2_tarski @ sk_A @ sk_B) @ X0) = (X0))
% 0.97/1.15          | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ X0))
% 0.97/1.15          | (r2_hidden @ (sk_C @ (k2_tarski @ sk_A @ sk_B) @ X0) @ 
% 0.97/1.15             (k1_tarski @ sk_C_1)))),
% 0.97/1.15      inference('sup-', [status(thm)], ['26', '27'])).
% 0.97/1.15  thf('29', plain,
% 0.97/1.15      (![X25 : $i, X28 : $i]:
% 0.97/1.15         (((X28) = (X25)) | ~ (r2_hidden @ X28 @ (k1_tarski @ X25)))),
% 0.97/1.15      inference('simplify', [status(thm)], ['19'])).
% 0.97/1.16  thf('30', plain,
% 0.97/1.16      (![X0 : $i]:
% 0.97/1.16         (((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ X0))
% 0.97/1.16          | ((sk_C @ (k2_tarski @ sk_A @ sk_B) @ X0) = (X0))
% 0.97/1.16          | ((sk_C @ (k2_tarski @ sk_A @ sk_B) @ X0) = (sk_C_1)))),
% 0.97/1.16      inference('sup-', [status(thm)], ['28', '29'])).
% 0.97/1.16  thf('31', plain,
% 0.97/1.16      (![X0 : $i]:
% 0.97/1.16         (((sk_C_1) != (X0))
% 0.97/1.16          | ((sk_C @ (k2_tarski @ sk_A @ sk_B) @ X0) = (X0))
% 0.97/1.16          | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ X0)))),
% 0.97/1.16      inference('eq_fact', [status(thm)], ['30'])).
% 0.97/1.16  thf('32', plain,
% 0.97/1.16      ((((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C_1))
% 0.97/1.16        | ((sk_C @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (sk_C_1)))),
% 0.97/1.16      inference('simplify', [status(thm)], ['31'])).
% 0.97/1.16  thf('33', plain, (((k2_tarski @ sk_A @ sk_B) != (k1_tarski @ sk_C_1))),
% 0.97/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.16  thf('34', plain, (((sk_C @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (sk_C_1))),
% 0.97/1.16      inference('simplify_reflect-', [status(thm)], ['32', '33'])).
% 0.97/1.16  thf('35', plain,
% 0.97/1.16      (![X25 : $i, X29 : $i]:
% 0.97/1.16         (((X29) = (k1_tarski @ X25))
% 0.97/1.16          | ((sk_C @ X29 @ X25) != (X25))
% 0.97/1.16          | ~ (r2_hidden @ (sk_C @ X29 @ X25) @ X29))),
% 0.97/1.16      inference('cnf', [status(esa)], [d1_tarski])).
% 0.97/1.16  thf('36', plain,
% 0.97/1.16      ((~ (r2_hidden @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.97/1.16        | ((sk_C @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) != (sk_C_1))
% 0.97/1.16        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C_1)))),
% 0.97/1.16      inference('sup-', [status(thm)], ['34', '35'])).
% 0.97/1.16  thf('37', plain, (((sk_C @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (sk_C_1))),
% 0.97/1.16      inference('simplify_reflect-', [status(thm)], ['32', '33'])).
% 0.97/1.16  thf('38', plain,
% 0.97/1.16      ((~ (r2_hidden @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.97/1.16        | ((sk_C_1) != (sk_C_1))
% 0.97/1.16        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C_1)))),
% 0.97/1.16      inference('demod', [status(thm)], ['36', '37'])).
% 0.97/1.16  thf('39', plain,
% 0.97/1.16      ((((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C_1))
% 0.97/1.16        | ~ (r2_hidden @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.97/1.16      inference('simplify', [status(thm)], ['38'])).
% 0.97/1.16  thf('40', plain, (((k2_tarski @ sk_A @ sk_B) != (k1_tarski @ sk_C_1))),
% 0.97/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.16  thf('41', plain, (~ (r2_hidden @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B))),
% 0.97/1.16      inference('simplify_reflect-', [status(thm)], ['39', '40'])).
% 0.97/1.16  thf('42', plain,
% 0.97/1.16      (![X0 : $i]:
% 0.97/1.16         ((k2_tarski @ sk_A @ sk_B)
% 0.97/1.16           = (k3_xboole_0 @ X0 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.97/1.16      inference('clc', [status(thm)], ['25', '41'])).
% 0.97/1.16  thf('43', plain,
% 0.97/1.16      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.97/1.16         (~ (r2_hidden @ X4 @ X3)
% 0.97/1.16          | (r2_hidden @ X4 @ X1)
% 0.97/1.16          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.97/1.16      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.97/1.16  thf('44', plain,
% 0.97/1.16      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.97/1.16         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.97/1.16      inference('simplify', [status(thm)], ['43'])).
% 0.97/1.16  thf('45', plain,
% 0.97/1.16      (![X0 : $i, X1 : $i]:
% 0.97/1.16         (~ (r2_hidden @ X1 @ (k2_tarski @ sk_A @ sk_B))
% 0.97/1.16          | (r2_hidden @ X1 @ X0))),
% 0.97/1.16      inference('sup-', [status(thm)], ['42', '44'])).
% 0.97/1.16  thf('46', plain, (![X0 : $i]: (r2_hidden @ sk_A @ X0)),
% 0.97/1.16      inference('sup-', [status(thm)], ['7', '45'])).
% 0.97/1.16  thf(t76_enumset1, axiom,
% 0.97/1.16    (![A:$i]: ( ( k1_enumset1 @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.97/1.16  thf('47', plain,
% 0.97/1.16      (![X48 : $i]: ((k1_enumset1 @ X48 @ X48 @ X48) = (k1_tarski @ X48))),
% 0.97/1.16      inference('cnf', [status(esa)], [t76_enumset1])).
% 0.97/1.16  thf('48', plain,
% 0.97/1.16      (![X30 : $i, X31 : $i]:
% 0.97/1.16         ((k1_enumset1 @ X30 @ X30 @ X31) = (k2_tarski @ X30 @ X31))),
% 0.97/1.16      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.97/1.16  thf('49', plain,
% 0.97/1.16      (![X48 : $i]: ((k2_tarski @ X48 @ X48) = (k1_tarski @ X48))),
% 0.97/1.16      inference('demod', [status(thm)], ['47', '48'])).
% 0.97/1.16  thf('50', plain,
% 0.97/1.16      (![X25 : $i, X28 : $i]:
% 0.97/1.16         (((X28) = (X25)) | ~ (r2_hidden @ X28 @ (k1_tarski @ X25)))),
% 0.97/1.16      inference('simplify', [status(thm)], ['19'])).
% 0.97/1.16  thf('51', plain,
% 0.97/1.16      (![X0 : $i, X1 : $i]:
% 0.97/1.16         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0)) | ((X1) = (X0)))),
% 0.97/1.16      inference('sup-', [status(thm)], ['49', '50'])).
% 0.97/1.16  thf('52', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.97/1.16      inference('sup-', [status(thm)], ['46', '51'])).
% 0.97/1.16  thf('53', plain,
% 0.97/1.16      (![X48 : $i]: ((k2_tarski @ X48 @ X48) = (k1_tarski @ X48))),
% 0.97/1.16      inference('demod', [status(thm)], ['47', '48'])).
% 0.97/1.16  thf('54', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.97/1.16      inference('sup-', [status(thm)], ['46', '51'])).
% 0.97/1.16  thf('55', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.97/1.16      inference('sup-', [status(thm)], ['46', '51'])).
% 0.97/1.16  thf('56', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.97/1.16      inference('sup-', [status(thm)], ['46', '51'])).
% 0.97/1.16  thf('57', plain, (((sk_A) != (sk_A))),
% 0.97/1.16      inference('demod', [status(thm)], ['0', '52', '53', '54', '55', '56'])).
% 0.97/1.16  thf('58', plain, ($false), inference('simplify', [status(thm)], ['57'])).
% 0.97/1.16  
% 0.97/1.16  % SZS output end Refutation
% 0.97/1.16  
% 0.97/1.16  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
