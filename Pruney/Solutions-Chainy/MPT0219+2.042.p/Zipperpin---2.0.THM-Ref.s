%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DLMLwYYTa5

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:09 EST 2020

% Result     : Theorem 0.85s
% Output     : Refutation 0.85s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 110 expanded)
%              Number of leaves         :   24 (  41 expanded)
%              Depth                    :   20
%              Number of atoms          :  620 ( 925 expanded)
%              Number of equality atoms :   47 (  77 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

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
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 @ X30 @ X31 )
      | ( X28 = X29 )
      | ( X28 = X30 )
      | ( X28 = X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t13_zfmisc_1])).

thf('1',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X39: $i] :
      ( ( k2_tarski @ X39 @ X39 )
      = ( k1_tarski @ X39 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_enumset1 @ X40 @ X40 @ X41 )
      = ( k2_tarski @ X40 @ X41 ) ) ),
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

thf('4',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 @ X34 @ X35 )
      | ( r2_hidden @ X32 @ X36 )
      | ( X36
       != ( k1_enumset1 @ X35 @ X34 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('5',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( r2_hidden @ X32 @ ( k1_enumset1 @ X35 @ X34 @ X33 ) )
      | ( zip_tseitin_0 @ X32 @ X33 @ X34 @ X35 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( X28 != X27 )
      | ~ ( zip_tseitin_0 @ X28 @ X29 @ X30 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X27: $i,X29: $i,X30: $i] :
      ~ ( zip_tseitin_0 @ X27 @ X29 @ X30 @ X27 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','9'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( r2_hidden @ X6 @ X8 )
      | ( r2_hidden @ X6 @ X9 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('12',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X6 @ ( k4_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 @ X30 @ X31 )
      | ( X28 = X29 )
      | ( X28 = X30 )
      | ( X28 = X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('15',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,(
    ! [X39: $i] :
      ( ( k2_tarski @ X39 @ X39 )
      = ( k1_tarski @ X39 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('17',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_enumset1 @ X40 @ X40 @ X41 )
      = ( k2_tarski @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('18',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X37 @ X36 )
      | ~ ( zip_tseitin_0 @ X37 @ X33 @ X34 @ X35 )
      | ( X36
       != ( k1_enumset1 @ X35 @ X34 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('19',plain,(
    ! [X33: $i,X34: $i,X35: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X33 @ X34 @ X35 )
      | ~ ( r2_hidden @ X37 @ ( k1_enumset1 @ X35 @ X34 @ X33 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( zip_tseitin_0 @ ( sk_C @ X1 @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','27'])).

thf('29',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('30',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X7 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('31',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('36',plain,(
    ! [X16: $i,X18: $i] :
      ( ( X16 = X18 )
      | ~ ( r1_tarski @ X18 @ X16 )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k1_tarski @ X1 )
        = ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','37'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('39',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','9'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('42',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ( r2_hidden @ X12 @ ( k5_xboole_0 @ X13 @ X15 ) )
      | ( r2_hidden @ X12 @ X13 )
      | ~ ( r2_hidden @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k5_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['1','45'])).

thf('47',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf('49',plain,(
    ~ ( zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_B = sk_A )
    | ( sk_B = sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['0','49'])).

thf('51',plain,(
    sk_B = sk_A ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('53',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['51','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DLMLwYYTa5
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:43:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.85/1.06  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.85/1.06  % Solved by: fo/fo7.sh
% 0.85/1.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.85/1.06  % done 1019 iterations in 0.607s
% 0.85/1.06  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.85/1.06  % SZS output start Refutation
% 0.85/1.06  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.85/1.06  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.85/1.06  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.85/1.06  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.85/1.06  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.85/1.06  thf(sk_B_type, type, sk_B: $i).
% 0.85/1.06  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.85/1.06  thf(sk_A_type, type, sk_A: $i).
% 0.85/1.06  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.85/1.06  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.85/1.06  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.85/1.06  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.85/1.06  thf(d1_enumset1, axiom,
% 0.85/1.06    (![A:$i,B:$i,C:$i,D:$i]:
% 0.85/1.06     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.85/1.06       ( ![E:$i]:
% 0.85/1.06         ( ( r2_hidden @ E @ D ) <=>
% 0.85/1.06           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.85/1.06  thf(zf_stmt_0, axiom,
% 0.85/1.06    (![E:$i,C:$i,B:$i,A:$i]:
% 0.85/1.06     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.85/1.06       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.85/1.06  thf('0', plain,
% 0.85/1.06      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.85/1.06         ((zip_tseitin_0 @ X28 @ X29 @ X30 @ X31)
% 0.85/1.06          | ((X28) = (X29))
% 0.85/1.06          | ((X28) = (X30))
% 0.85/1.06          | ((X28) = (X31)))),
% 0.85/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.06  thf(t13_zfmisc_1, conjecture,
% 0.85/1.06    (![A:$i,B:$i]:
% 0.85/1.06     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.85/1.06         ( k1_tarski @ A ) ) =>
% 0.85/1.06       ( ( A ) = ( B ) ) ))).
% 0.85/1.06  thf(zf_stmt_1, negated_conjecture,
% 0.85/1.06    (~( ![A:$i,B:$i]:
% 0.85/1.06        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.85/1.06            ( k1_tarski @ A ) ) =>
% 0.85/1.06          ( ( A ) = ( B ) ) ) )),
% 0.85/1.06    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 0.85/1.06  thf('1', plain,
% 0.85/1.06      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.85/1.06         = (k1_tarski @ sk_A))),
% 0.85/1.06      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.85/1.06  thf(t69_enumset1, axiom,
% 0.85/1.06    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.85/1.06  thf('2', plain, (![X39 : $i]: ((k2_tarski @ X39 @ X39) = (k1_tarski @ X39))),
% 0.85/1.06      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.85/1.06  thf(t70_enumset1, axiom,
% 0.85/1.06    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.85/1.06  thf('3', plain,
% 0.85/1.06      (![X40 : $i, X41 : $i]:
% 0.85/1.06         ((k1_enumset1 @ X40 @ X40 @ X41) = (k2_tarski @ X40 @ X41))),
% 0.85/1.06      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.85/1.06  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.85/1.06  thf(zf_stmt_3, axiom,
% 0.85/1.06    (![A:$i,B:$i,C:$i,D:$i]:
% 0.85/1.06     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.85/1.06       ( ![E:$i]:
% 0.85/1.06         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.85/1.06  thf('4', plain,
% 0.85/1.06      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.85/1.06         ((zip_tseitin_0 @ X32 @ X33 @ X34 @ X35)
% 0.85/1.06          | (r2_hidden @ X32 @ X36)
% 0.85/1.06          | ((X36) != (k1_enumset1 @ X35 @ X34 @ X33)))),
% 0.85/1.06      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.85/1.06  thf('5', plain,
% 0.85/1.06      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.85/1.06         ((r2_hidden @ X32 @ (k1_enumset1 @ X35 @ X34 @ X33))
% 0.85/1.06          | (zip_tseitin_0 @ X32 @ X33 @ X34 @ X35))),
% 0.85/1.06      inference('simplify', [status(thm)], ['4'])).
% 0.85/1.06  thf('6', plain,
% 0.85/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.06         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.85/1.06          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.85/1.06      inference('sup+', [status(thm)], ['3', '5'])).
% 0.85/1.06  thf('7', plain,
% 0.85/1.06      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.85/1.06         (((X28) != (X27)) | ~ (zip_tseitin_0 @ X28 @ X29 @ X30 @ X27))),
% 0.85/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.06  thf('8', plain,
% 0.85/1.06      (![X27 : $i, X29 : $i, X30 : $i]:
% 0.85/1.06         ~ (zip_tseitin_0 @ X27 @ X29 @ X30 @ X27)),
% 0.85/1.06      inference('simplify', [status(thm)], ['7'])).
% 0.85/1.06  thf('9', plain,
% 0.85/1.06      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.85/1.06      inference('sup-', [status(thm)], ['6', '8'])).
% 0.85/1.06  thf('10', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.85/1.06      inference('sup+', [status(thm)], ['2', '9'])).
% 0.85/1.06  thf(d5_xboole_0, axiom,
% 0.85/1.06    (![A:$i,B:$i,C:$i]:
% 0.85/1.06     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.85/1.06       ( ![D:$i]:
% 0.85/1.06         ( ( r2_hidden @ D @ C ) <=>
% 0.85/1.06           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.85/1.06  thf('11', plain,
% 0.85/1.06      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.85/1.06         (~ (r2_hidden @ X6 @ X7)
% 0.85/1.06          | (r2_hidden @ X6 @ X8)
% 0.85/1.06          | (r2_hidden @ X6 @ X9)
% 0.85/1.06          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.85/1.06      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.85/1.06  thf('12', plain,
% 0.85/1.06      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.85/1.06         ((r2_hidden @ X6 @ (k4_xboole_0 @ X7 @ X8))
% 0.85/1.06          | (r2_hidden @ X6 @ X8)
% 0.85/1.06          | ~ (r2_hidden @ X6 @ X7))),
% 0.85/1.06      inference('simplify', [status(thm)], ['11'])).
% 0.85/1.06  thf('13', plain,
% 0.85/1.06      (![X0 : $i, X1 : $i]:
% 0.85/1.06         ((r2_hidden @ X0 @ X1)
% 0.85/1.06          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.85/1.06      inference('sup-', [status(thm)], ['10', '12'])).
% 0.85/1.06  thf('14', plain,
% 0.85/1.06      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.85/1.06         ((zip_tseitin_0 @ X28 @ X29 @ X30 @ X31)
% 0.85/1.06          | ((X28) = (X29))
% 0.85/1.06          | ((X28) = (X30))
% 0.85/1.06          | ((X28) = (X31)))),
% 0.85/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.06  thf(d3_tarski, axiom,
% 0.85/1.06    (![A:$i,B:$i]:
% 0.85/1.06     ( ( r1_tarski @ A @ B ) <=>
% 0.85/1.06       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.85/1.06  thf('15', plain,
% 0.85/1.06      (![X3 : $i, X5 : $i]:
% 0.85/1.06         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.85/1.06      inference('cnf', [status(esa)], [d3_tarski])).
% 0.85/1.06  thf('16', plain,
% 0.85/1.06      (![X39 : $i]: ((k2_tarski @ X39 @ X39) = (k1_tarski @ X39))),
% 0.85/1.06      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.85/1.06  thf('17', plain,
% 0.85/1.06      (![X40 : $i, X41 : $i]:
% 0.85/1.06         ((k1_enumset1 @ X40 @ X40 @ X41) = (k2_tarski @ X40 @ X41))),
% 0.85/1.06      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.85/1.06  thf('18', plain,
% 0.85/1.06      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.85/1.06         (~ (r2_hidden @ X37 @ X36)
% 0.85/1.06          | ~ (zip_tseitin_0 @ X37 @ X33 @ X34 @ X35)
% 0.85/1.06          | ((X36) != (k1_enumset1 @ X35 @ X34 @ X33)))),
% 0.85/1.06      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.85/1.06  thf('19', plain,
% 0.85/1.06      (![X33 : $i, X34 : $i, X35 : $i, X37 : $i]:
% 0.85/1.06         (~ (zip_tseitin_0 @ X37 @ X33 @ X34 @ X35)
% 0.85/1.06          | ~ (r2_hidden @ X37 @ (k1_enumset1 @ X35 @ X34 @ X33)))),
% 0.85/1.06      inference('simplify', [status(thm)], ['18'])).
% 0.85/1.06  thf('20', plain,
% 0.85/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.06         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.85/1.06          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.85/1.06      inference('sup-', [status(thm)], ['17', '19'])).
% 0.85/1.06  thf('21', plain,
% 0.85/1.06      (![X0 : $i, X1 : $i]:
% 0.85/1.06         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.85/1.06          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.85/1.06      inference('sup-', [status(thm)], ['16', '20'])).
% 0.85/1.06  thf('22', plain,
% 0.85/1.06      (![X0 : $i, X1 : $i]:
% 0.85/1.06         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.85/1.06          | ~ (zip_tseitin_0 @ (sk_C @ X1 @ (k1_tarski @ X0)) @ X0 @ X0 @ X0))),
% 0.85/1.06      inference('sup-', [status(thm)], ['15', '21'])).
% 0.85/1.06  thf('23', plain,
% 0.85/1.06      (![X0 : $i, X1 : $i]:
% 0.85/1.06         (((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.85/1.06          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.85/1.06          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.85/1.06          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.85/1.06      inference('sup-', [status(thm)], ['14', '22'])).
% 0.85/1.06  thf('24', plain,
% 0.85/1.06      (![X0 : $i, X1 : $i]:
% 0.85/1.06         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.85/1.06          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.85/1.06      inference('simplify', [status(thm)], ['23'])).
% 0.85/1.06  thf('25', plain,
% 0.85/1.06      (![X3 : $i, X5 : $i]:
% 0.85/1.06         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.85/1.06      inference('cnf', [status(esa)], [d3_tarski])).
% 0.85/1.06  thf('26', plain,
% 0.85/1.06      (![X0 : $i, X1 : $i]:
% 0.85/1.06         (~ (r2_hidden @ X0 @ X1)
% 0.85/1.06          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.85/1.06          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.85/1.06      inference('sup-', [status(thm)], ['24', '25'])).
% 0.85/1.06  thf('27', plain,
% 0.85/1.06      (![X0 : $i, X1 : $i]:
% 0.85/1.06         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.85/1.06      inference('simplify', [status(thm)], ['26'])).
% 0.85/1.06  thf('28', plain,
% 0.85/1.06      (![X0 : $i, X1 : $i]:
% 0.85/1.06         ((r2_hidden @ X1 @ X0)
% 0.85/1.06          | (r1_tarski @ (k1_tarski @ X1) @ 
% 0.85/1.06             (k4_xboole_0 @ (k1_tarski @ X1) @ X0)))),
% 0.85/1.06      inference('sup-', [status(thm)], ['13', '27'])).
% 0.85/1.06  thf('29', plain,
% 0.85/1.06      (![X3 : $i, X5 : $i]:
% 0.85/1.06         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.85/1.06      inference('cnf', [status(esa)], [d3_tarski])).
% 0.85/1.06  thf('30', plain,
% 0.85/1.06      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.85/1.06         (~ (r2_hidden @ X10 @ X9)
% 0.85/1.06          | (r2_hidden @ X10 @ X7)
% 0.85/1.06          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.85/1.06      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.85/1.06  thf('31', plain,
% 0.85/1.06      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.85/1.06         ((r2_hidden @ X10 @ X7)
% 0.85/1.06          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.85/1.06      inference('simplify', [status(thm)], ['30'])).
% 0.85/1.06  thf('32', plain,
% 0.85/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.06         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.85/1.06          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.85/1.06      inference('sup-', [status(thm)], ['29', '31'])).
% 0.85/1.06  thf('33', plain,
% 0.85/1.06      (![X3 : $i, X5 : $i]:
% 0.85/1.06         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.85/1.06      inference('cnf', [status(esa)], [d3_tarski])).
% 0.85/1.06  thf('34', plain,
% 0.85/1.06      (![X0 : $i, X1 : $i]:
% 0.85/1.06         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.85/1.06          | (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.85/1.06      inference('sup-', [status(thm)], ['32', '33'])).
% 0.85/1.06  thf('35', plain,
% 0.85/1.06      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.85/1.06      inference('simplify', [status(thm)], ['34'])).
% 0.85/1.06  thf(d10_xboole_0, axiom,
% 0.85/1.06    (![A:$i,B:$i]:
% 0.85/1.06     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.85/1.06  thf('36', plain,
% 0.85/1.06      (![X16 : $i, X18 : $i]:
% 0.85/1.06         (((X16) = (X18))
% 0.85/1.06          | ~ (r1_tarski @ X18 @ X16)
% 0.85/1.06          | ~ (r1_tarski @ X16 @ X18))),
% 0.85/1.06      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.85/1.06  thf('37', plain,
% 0.85/1.06      (![X0 : $i, X1 : $i]:
% 0.85/1.06         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.85/1.06          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.85/1.06      inference('sup-', [status(thm)], ['35', '36'])).
% 0.85/1.06  thf('38', plain,
% 0.85/1.06      (![X0 : $i, X1 : $i]:
% 0.85/1.06         ((r2_hidden @ X1 @ X0)
% 0.85/1.06          | ((k1_tarski @ X1) = (k4_xboole_0 @ (k1_tarski @ X1) @ X0)))),
% 0.85/1.06      inference('sup-', [status(thm)], ['28', '37'])).
% 0.85/1.06  thf(t98_xboole_1, axiom,
% 0.85/1.06    (![A:$i,B:$i]:
% 0.85/1.06     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.85/1.06  thf('39', plain,
% 0.85/1.06      (![X25 : $i, X26 : $i]:
% 0.85/1.06         ((k2_xboole_0 @ X25 @ X26)
% 0.85/1.06           = (k5_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X25)))),
% 0.85/1.06      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.85/1.06  thf('40', plain,
% 0.85/1.06      (![X0 : $i, X1 : $i]:
% 0.85/1.06         (((k2_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.85/1.06            = (k5_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.85/1.06          | (r2_hidden @ X0 @ X1))),
% 0.85/1.06      inference('sup+', [status(thm)], ['38', '39'])).
% 0.85/1.06  thf('41', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.85/1.06      inference('sup+', [status(thm)], ['2', '9'])).
% 0.85/1.06  thf(t1_xboole_0, axiom,
% 0.85/1.06    (![A:$i,B:$i,C:$i]:
% 0.85/1.06     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.85/1.06       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.85/1.06  thf('42', plain,
% 0.85/1.06      (![X12 : $i, X13 : $i, X15 : $i]:
% 0.85/1.06         ((r2_hidden @ X12 @ (k5_xboole_0 @ X13 @ X15))
% 0.85/1.06          | (r2_hidden @ X12 @ X13)
% 0.85/1.06          | ~ (r2_hidden @ X12 @ X15))),
% 0.85/1.06      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.85/1.06  thf('43', plain,
% 0.85/1.06      (![X0 : $i, X1 : $i]:
% 0.85/1.06         ((r2_hidden @ X0 @ X1)
% 0.85/1.06          | (r2_hidden @ X0 @ (k5_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 0.85/1.06      inference('sup-', [status(thm)], ['41', '42'])).
% 0.85/1.06  thf('44', plain,
% 0.85/1.06      (![X0 : $i, X1 : $i]:
% 0.85/1.06         ((r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.85/1.06          | (r2_hidden @ X0 @ X1)
% 0.85/1.06          | (r2_hidden @ X0 @ X1))),
% 0.85/1.06      inference('sup+', [status(thm)], ['40', '43'])).
% 0.85/1.06  thf('45', plain,
% 0.85/1.06      (![X0 : $i, X1 : $i]:
% 0.85/1.06         ((r2_hidden @ X0 @ X1)
% 0.85/1.06          | (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 0.85/1.06      inference('simplify', [status(thm)], ['44'])).
% 0.85/1.06  thf('46', plain,
% 0.85/1.06      (((r2_hidden @ sk_B @ (k1_tarski @ sk_A))
% 0.85/1.06        | (r2_hidden @ sk_B @ (k1_tarski @ sk_A)))),
% 0.85/1.06      inference('sup+', [status(thm)], ['1', '45'])).
% 0.85/1.06  thf('47', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 0.85/1.06      inference('simplify', [status(thm)], ['46'])).
% 0.85/1.06  thf('48', plain,
% 0.85/1.06      (![X0 : $i, X1 : $i]:
% 0.85/1.06         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.85/1.06          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.85/1.06      inference('sup-', [status(thm)], ['16', '20'])).
% 0.85/1.06  thf('49', plain, (~ (zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A)),
% 0.85/1.06      inference('sup-', [status(thm)], ['47', '48'])).
% 0.85/1.06  thf('50', plain,
% 0.85/1.06      ((((sk_B) = (sk_A)) | ((sk_B) = (sk_A)) | ((sk_B) = (sk_A)))),
% 0.85/1.06      inference('sup-', [status(thm)], ['0', '49'])).
% 0.85/1.06  thf('51', plain, (((sk_B) = (sk_A))),
% 0.85/1.06      inference('simplify', [status(thm)], ['50'])).
% 0.85/1.06  thf('52', plain, (((sk_A) != (sk_B))),
% 0.85/1.06      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.85/1.06  thf('53', plain, ($false),
% 0.85/1.06      inference('simplify_reflect-', [status(thm)], ['51', '52'])).
% 0.85/1.06  
% 0.85/1.06  % SZS output end Refutation
% 0.85/1.06  
% 0.85/1.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
