%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9axlYcwFwg

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:55 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 151 expanded)
%              Number of leaves         :   24 (  54 expanded)
%              Depth                    :   22
%              Number of atoms          :  629 (1196 expanded)
%              Number of equality atoms :   72 ( 134 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 )
      | ( X17 = X18 )
      | ( X17 = X19 )
      | ( X17 = X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t21_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = k1_xboole_0 )
     => ( A = B ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = k1_xboole_0 )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t21_zfmisc_1])).

thf('1',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 )
      | ( X17 = X18 )
      | ( X17 = X19 )
      | ( X17 = X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('11',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['3','14'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('16',plain,(
    ! [X28: $i] :
      ( ( k2_tarski @ X28 @ X28 )
      = ( k1_tarski @ X28 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_enumset1 @ X29 @ X29 @ X30 )
      = ( k2_tarski @ X29 @ X30 ) ) ),
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

thf('18',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X26 @ X25 )
      | ~ ( zip_tseitin_0 @ X26 @ X22 @ X23 @ X24 )
      | ( X25
       != ( k1_enumset1 @ X24 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('19',plain,(
    ! [X22: $i,X23: $i,X24: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X22 @ X23 @ X24 )
      | ~ ( r2_hidden @ X26 @ ( k1_enumset1 @ X24 @ X23 @ X22 ) ) ) ),
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
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ~ ( zip_tseitin_0 @ ( sk_D @ k1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ k1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_D @ k1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_D @ k1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['2','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( sk_D @ k1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['3','14'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('29',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('35',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,
    ( ( r2_hidden @ sk_A @ k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( k1_xboole_0
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['1','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('39',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf('41',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( k1_xboole_0
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','41'])).

thf('43',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ sk_A ) )
    | ( sk_A = sk_B ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('45',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X28: $i] :
      ( ( k2_tarski @ X28 @ X28 )
      = ( k1_tarski @ X28 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('47',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_enumset1 @ X29 @ X29 @ X30 )
      = ( k2_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('48',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X24 )
      | ( r2_hidden @ X21 @ X25 )
      | ( X25
       != ( k1_enumset1 @ X24 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('49',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ X21 @ ( k1_enumset1 @ X24 @ X23 @ X22 ) )
      | ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X24 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['47','49'])).

thf('51',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X17 != X16 )
      | ~ ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ~ ( zip_tseitin_0 @ X16 @ X18 @ X19 @ X16 ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','53'])).

thf('55',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['45','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('57',plain,(
    $false ),
    inference('sup-',[status(thm)],['55','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9axlYcwFwg
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:08:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.64  % Solved by: fo/fo7.sh
% 0.46/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.64  % done 266 iterations in 0.191s
% 0.46/0.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.64  % SZS output start Refutation
% 0.46/0.64  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.46/0.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.46/0.64  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.64  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.64  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.64  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.46/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.64  thf(d1_enumset1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.64     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.46/0.64       ( ![E:$i]:
% 0.46/0.64         ( ( r2_hidden @ E @ D ) <=>
% 0.46/0.64           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.46/0.64  thf(zf_stmt_0, axiom,
% 0.46/0.64    (![E:$i,C:$i,B:$i,A:$i]:
% 0.46/0.64     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.46/0.64       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.46/0.64  thf('0', plain,
% 0.46/0.64      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.64         ((zip_tseitin_0 @ X17 @ X18 @ X19 @ X20)
% 0.46/0.64          | ((X17) = (X18))
% 0.46/0.64          | ((X17) = (X19))
% 0.46/0.64          | ((X17) = (X20)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(t21_zfmisc_1, conjecture,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.46/0.64         ( k1_xboole_0 ) ) =>
% 0.46/0.64       ( ( A ) = ( B ) ) ))).
% 0.46/0.64  thf(zf_stmt_1, negated_conjecture,
% 0.46/0.64    (~( ![A:$i,B:$i]:
% 0.46/0.64        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.46/0.64            ( k1_xboole_0 ) ) =>
% 0.46/0.64          ( ( A ) = ( B ) ) ) )),
% 0.46/0.64    inference('cnf.neg', [status(esa)], [t21_zfmisc_1])).
% 0.46/0.64  thf('1', plain,
% 0.46/0.64      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.64  thf('2', plain,
% 0.46/0.64      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.64         ((zip_tseitin_0 @ X17 @ X18 @ X19 @ X20)
% 0.46/0.64          | ((X17) = (X18))
% 0.46/0.64          | ((X17) = (X19))
% 0.46/0.64          | ((X17) = (X20)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(d5_xboole_0, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.46/0.64       ( ![D:$i]:
% 0.46/0.64         ( ( r2_hidden @ D @ C ) <=>
% 0.46/0.64           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.46/0.64  thf('3', plain,
% 0.46/0.64      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.46/0.64         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 0.46/0.64          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.46/0.64          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.46/0.64      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.46/0.64  thf(t2_boole, axiom,
% 0.46/0.64    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.46/0.64  thf('4', plain,
% 0.46/0.64      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.64      inference('cnf', [status(esa)], [t2_boole])).
% 0.46/0.64  thf(t100_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.64  thf('5', plain,
% 0.46/0.64      (![X8 : $i, X9 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X8 @ X9)
% 0.46/0.64           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.64  thf(commutativity_k5_xboole_0, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.46/0.64  thf('6', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.46/0.64  thf(t5_boole, axiom,
% 0.46/0.64    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.64  thf('7', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.46/0.64      inference('cnf', [status(esa)], [t5_boole])).
% 0.46/0.64  thf('8', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['6', '7'])).
% 0.46/0.64  thf('9', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['5', '8'])).
% 0.46/0.64  thf('10', plain,
% 0.46/0.64      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X6 @ X5)
% 0.46/0.64          | ~ (r2_hidden @ X6 @ X4)
% 0.46/0.64          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.46/0.64      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.46/0.64  thf('11', plain,
% 0.46/0.64      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X6 @ X4)
% 0.46/0.64          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['10'])).
% 0.46/0.64  thf('12', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X1 @ (k3_xboole_0 @ k1_xboole_0 @ X0))
% 0.46/0.64          | ~ (r2_hidden @ X1 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['9', '11'])).
% 0.46/0.64  thf('13', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['4', '12'])).
% 0.46/0.64  thf('14', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.46/0.64      inference('simplify', [status(thm)], ['13'])).
% 0.46/0.64  thf('15', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.46/0.64          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['3', '14'])).
% 0.46/0.64  thf(t69_enumset1, axiom,
% 0.46/0.64    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.46/0.64  thf('16', plain,
% 0.46/0.64      (![X28 : $i]: ((k2_tarski @ X28 @ X28) = (k1_tarski @ X28))),
% 0.46/0.64      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.64  thf(t70_enumset1, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.46/0.64  thf('17', plain,
% 0.46/0.64      (![X29 : $i, X30 : $i]:
% 0.46/0.64         ((k1_enumset1 @ X29 @ X29 @ X30) = (k2_tarski @ X29 @ X30))),
% 0.46/0.64      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.46/0.64  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.46/0.64  thf(zf_stmt_3, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.64     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.46/0.64       ( ![E:$i]:
% 0.46/0.64         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.46/0.64  thf('18', plain,
% 0.46/0.64      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X26 @ X25)
% 0.46/0.64          | ~ (zip_tseitin_0 @ X26 @ X22 @ X23 @ X24)
% 0.46/0.64          | ((X25) != (k1_enumset1 @ X24 @ X23 @ X22)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.64  thf('19', plain,
% 0.46/0.64      (![X22 : $i, X23 : $i, X24 : $i, X26 : $i]:
% 0.46/0.64         (~ (zip_tseitin_0 @ X26 @ X22 @ X23 @ X24)
% 0.46/0.64          | ~ (r2_hidden @ X26 @ (k1_enumset1 @ X24 @ X23 @ X22)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['18'])).
% 0.46/0.64  thf('20', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.46/0.64          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['17', '19'])).
% 0.46/0.64  thf('21', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.46/0.64          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['16', '20'])).
% 0.46/0.64  thf('22', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.46/0.64          | ~ (zip_tseitin_0 @ (sk_D @ k1_xboole_0 @ X1 @ (k1_tarski @ X0)) @ 
% 0.46/0.64               X0 @ X0 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['15', '21'])).
% 0.46/0.64  thf('23', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((sk_D @ k1_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.46/0.64          | ((sk_D @ k1_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.46/0.64          | ((sk_D @ k1_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.46/0.64          | ((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['2', '22'])).
% 0.46/0.64  thf('24', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.46/0.64          | ((sk_D @ k1_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['23'])).
% 0.46/0.64  thf('25', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.46/0.64          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['3', '14'])).
% 0.46/0.64  thf('26', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.46/0.64          | ((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.46/0.64          | ((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['24', '25'])).
% 0.46/0.64  thf('27', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.46/0.64          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['26'])).
% 0.46/0.64  thf('28', plain,
% 0.46/0.64      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.64      inference('cnf', [status(esa)], [t2_boole])).
% 0.46/0.64  thf('29', plain,
% 0.46/0.64      (![X8 : $i, X9 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X8 @ X9)
% 0.46/0.64           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.64  thf('30', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['28', '29'])).
% 0.46/0.64  thf('31', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.46/0.64      inference('cnf', [status(esa)], [t5_boole])).
% 0.46/0.64  thf('32', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['30', '31'])).
% 0.46/0.64  thf('33', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((k1_xboole_0) = (k1_tarski @ X0))
% 0.46/0.64          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['27', '32'])).
% 0.46/0.64  thf('34', plain,
% 0.46/0.64      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X2 @ X3)
% 0.46/0.64          | (r2_hidden @ X2 @ X4)
% 0.46/0.64          | (r2_hidden @ X2 @ X5)
% 0.46/0.64          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.46/0.64      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.46/0.64  thf('35', plain,
% 0.46/0.64      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.64         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 0.46/0.64          | (r2_hidden @ X2 @ X4)
% 0.46/0.64          | ~ (r2_hidden @ X2 @ X3))),
% 0.46/0.64      inference('simplify', [status(thm)], ['34'])).
% 0.46/0.64  thf('36', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((k1_xboole_0) = (k1_tarski @ X0))
% 0.46/0.64          | (r2_hidden @ X0 @ X1)
% 0.46/0.64          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['33', '35'])).
% 0.46/0.64  thf('37', plain,
% 0.46/0.64      (((r2_hidden @ sk_A @ k1_xboole_0)
% 0.46/0.64        | (r2_hidden @ sk_A @ (k1_tarski @ sk_B))
% 0.46/0.64        | ((k1_xboole_0) = (k1_tarski @ sk_A)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['1', '36'])).
% 0.46/0.64  thf('38', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.46/0.64      inference('simplify', [status(thm)], ['13'])).
% 0.46/0.64  thf('39', plain,
% 0.46/0.64      ((((k1_xboole_0) = (k1_tarski @ sk_A))
% 0.46/0.64        | (r2_hidden @ sk_A @ (k1_tarski @ sk_B)))),
% 0.46/0.64      inference('clc', [status(thm)], ['37', '38'])).
% 0.46/0.64  thf('40', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.46/0.64          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['16', '20'])).
% 0.46/0.64  thf('41', plain,
% 0.46/0.64      ((((k1_xboole_0) = (k1_tarski @ sk_A))
% 0.46/0.64        | ~ (zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B))),
% 0.46/0.64      inference('sup-', [status(thm)], ['39', '40'])).
% 0.46/0.64  thf('42', plain,
% 0.46/0.64      ((((sk_A) = (sk_B))
% 0.46/0.64        | ((sk_A) = (sk_B))
% 0.46/0.64        | ((sk_A) = (sk_B))
% 0.46/0.64        | ((k1_xboole_0) = (k1_tarski @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['0', '41'])).
% 0.46/0.64  thf('43', plain,
% 0.46/0.64      ((((k1_xboole_0) = (k1_tarski @ sk_A)) | ((sk_A) = (sk_B)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['42'])).
% 0.46/0.64  thf('44', plain, (((sk_A) != (sk_B))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.64  thf('45', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['43', '44'])).
% 0.46/0.64  thf('46', plain,
% 0.46/0.64      (![X28 : $i]: ((k2_tarski @ X28 @ X28) = (k1_tarski @ X28))),
% 0.46/0.64      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.64  thf('47', plain,
% 0.46/0.64      (![X29 : $i, X30 : $i]:
% 0.46/0.64         ((k1_enumset1 @ X29 @ X29 @ X30) = (k2_tarski @ X29 @ X30))),
% 0.46/0.64      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.46/0.64  thf('48', plain,
% 0.46/0.64      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.46/0.64         ((zip_tseitin_0 @ X21 @ X22 @ X23 @ X24)
% 0.46/0.64          | (r2_hidden @ X21 @ X25)
% 0.46/0.64          | ((X25) != (k1_enumset1 @ X24 @ X23 @ X22)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.64  thf('49', plain,
% 0.46/0.64      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.46/0.64         ((r2_hidden @ X21 @ (k1_enumset1 @ X24 @ X23 @ X22))
% 0.46/0.64          | (zip_tseitin_0 @ X21 @ X22 @ X23 @ X24))),
% 0.46/0.64      inference('simplify', [status(thm)], ['48'])).
% 0.46/0.64  thf('50', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.46/0.64          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.46/0.64      inference('sup+', [status(thm)], ['47', '49'])).
% 0.46/0.64  thf('51', plain,
% 0.46/0.64      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.64         (((X17) != (X16)) | ~ (zip_tseitin_0 @ X17 @ X18 @ X19 @ X16))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('52', plain,
% 0.46/0.64      (![X16 : $i, X18 : $i, X19 : $i]:
% 0.46/0.64         ~ (zip_tseitin_0 @ X16 @ X18 @ X19 @ X16)),
% 0.46/0.64      inference('simplify', [status(thm)], ['51'])).
% 0.46/0.64  thf('53', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['50', '52'])).
% 0.46/0.64  thf('54', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['46', '53'])).
% 0.46/0.64  thf('55', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.46/0.64      inference('sup+', [status(thm)], ['45', '54'])).
% 0.46/0.64  thf('56', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.46/0.64      inference('simplify', [status(thm)], ['13'])).
% 0.46/0.64  thf('57', plain, ($false), inference('sup-', [status(thm)], ['55', '56'])).
% 0.46/0.64  
% 0.46/0.64  % SZS output end Refutation
% 0.46/0.64  
% 0.46/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
