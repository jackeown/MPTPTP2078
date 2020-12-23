%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.R0s8oWO5im

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:42 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 111 expanded)
%              Number of leaves         :   24 (  43 expanded)
%              Depth                    :   12
%              Number of atoms          :  629 ( 995 expanded)
%              Number of equality atoms :   45 (  75 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t59_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = ( k1_tarski @ A ) )
        & ( r2_hidden @ B @ C )
        & ( A != B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
            = ( k1_tarski @ A ) )
          & ( r2_hidden @ B @ C )
          & ( A != B ) ) ),
    inference('cnf.neg',[status(esa)],[t59_zfmisc_1])).

thf('0',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('2',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_enumset1 @ X25 @ X25 @ X26 )
      = ( k2_tarski @ X25 @ X26 ) ) ),
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

thf('4',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 )
      | ( r2_hidden @ X17 @ X21 )
      | ( X21
       != ( k1_enumset1 @ X20 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('5',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X17 @ ( k1_enumset1 @ X20 @ X19 @ X18 ) )
      | ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X13 != X14 )
      | ~ ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ~ ( zip_tseitin_0 @ X14 @ X14 @ X15 @ X12 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k5_xboole_0 @ X1 @ X3 ) )
      | ( r2_hidden @ X0 @ X3 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ ( k5_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r2_hidden @ sk_B @ ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','11'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('15',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('16',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('21',plain,(
    r2_hidden @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference(clc,[status(thm)],['12','24'])).

thf('26',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 )
      | ( X13 = X14 )
      | ( X13 = X15 )
      | ( X13 = X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('27',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('28',plain,(
    ! [X24: $i] :
      ( ( k2_tarski @ X24 @ X24 )
      = ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('29',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_enumset1 @ X25 @ X25 @ X26 )
      = ( k2_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('30',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X22 @ X21 )
      | ~ ( zip_tseitin_0 @ X22 @ X18 @ X19 @ X20 )
      | ( X21
       != ( k1_enumset1 @ X20 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('31',plain,(
    ! [X18: $i,X19: $i,X20: $i,X22: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X18 @ X19 @ X20 )
      | ~ ( r2_hidden @ X22 @ ( k1_enumset1 @ X20 @ X19 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( zip_tseitin_0 @ ( sk_C @ X1 @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 )
      | ( X13 = X14 )
      | ( X13 = X15 )
      | ( X13 = X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('38',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','32'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( sk_C @ ( k1_tarski @ X0 ) @ X1 ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ ( k1_tarski @ X0 ) @ X1 )
        = X0 )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ X1 )
        = X0 )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ X1 )
        = X0 )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['36','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X24: $i] :
      ( ( k2_tarski @ X24 @ X24 )
      = ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('47',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X13 != X12 )
      | ~ ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('48',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ~ ( zip_tseitin_0 @ X12 @ X14 @ X15 @ X12 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','49'])).

thf('51',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','52'])).

thf('54',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['25','53'])).

thf('55',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['54','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.R0s8oWO5im
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:40:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.60/0.79  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.60/0.79  % Solved by: fo/fo7.sh
% 0.60/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.79  % done 668 iterations in 0.369s
% 0.60/0.79  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.60/0.79  % SZS output start Refutation
% 0.60/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.79  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.79  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.60/0.79  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.60/0.79  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.60/0.79  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.60/0.79  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.60/0.79  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.60/0.79  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.60/0.79  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.60/0.79  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.60/0.79  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.60/0.79  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.60/0.79  thf(t59_zfmisc_1, conjecture,
% 0.60/0.79    (![A:$i,B:$i,C:$i]:
% 0.60/0.79     ( ~( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) & 
% 0.60/0.79          ( r2_hidden @ B @ C ) & ( ( A ) != ( B ) ) ) ))).
% 0.60/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.79    (~( ![A:$i,B:$i,C:$i]:
% 0.60/0.79        ( ~( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) & 
% 0.60/0.79             ( r2_hidden @ B @ C ) & ( ( A ) != ( B ) ) ) ) )),
% 0.60/0.79    inference('cnf.neg', [status(esa)], [t59_zfmisc_1])).
% 0.60/0.79  thf('0', plain,
% 0.60/0.79      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_tarski @ sk_A))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf(t100_xboole_1, axiom,
% 0.60/0.79    (![A:$i,B:$i]:
% 0.60/0.79     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.60/0.79  thf('1', plain,
% 0.60/0.79      (![X8 : $i, X9 : $i]:
% 0.60/0.79         ((k4_xboole_0 @ X8 @ X9)
% 0.60/0.79           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.60/0.79      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.60/0.79  thf('2', plain,
% 0.60/0.79      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.60/0.79         = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.60/0.79      inference('sup+', [status(thm)], ['0', '1'])).
% 0.60/0.79  thf(t70_enumset1, axiom,
% 0.60/0.79    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.60/0.79  thf('3', plain,
% 0.60/0.79      (![X25 : $i, X26 : $i]:
% 0.60/0.79         ((k1_enumset1 @ X25 @ X25 @ X26) = (k2_tarski @ X25 @ X26))),
% 0.60/0.79      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.60/0.79  thf(d1_enumset1, axiom,
% 0.60/0.79    (![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.79     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.60/0.79       ( ![E:$i]:
% 0.60/0.79         ( ( r2_hidden @ E @ D ) <=>
% 0.60/0.79           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.60/0.79  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.60/0.79  thf(zf_stmt_2, axiom,
% 0.60/0.79    (![E:$i,C:$i,B:$i,A:$i]:
% 0.60/0.79     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.60/0.79       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.60/0.79  thf(zf_stmt_3, axiom,
% 0.60/0.79    (![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.79     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.60/0.79       ( ![E:$i]:
% 0.60/0.79         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.60/0.79  thf('4', plain,
% 0.60/0.79      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.60/0.79         ((zip_tseitin_0 @ X17 @ X18 @ X19 @ X20)
% 0.60/0.79          | (r2_hidden @ X17 @ X21)
% 0.60/0.79          | ((X21) != (k1_enumset1 @ X20 @ X19 @ X18)))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.79  thf('5', plain,
% 0.60/0.79      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.60/0.79         ((r2_hidden @ X17 @ (k1_enumset1 @ X20 @ X19 @ X18))
% 0.60/0.79          | (zip_tseitin_0 @ X17 @ X18 @ X19 @ X20))),
% 0.60/0.79      inference('simplify', [status(thm)], ['4'])).
% 0.60/0.79  thf('6', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.79         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.60/0.79          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.60/0.79      inference('sup+', [status(thm)], ['3', '5'])).
% 0.60/0.79  thf('7', plain,
% 0.60/0.79      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.60/0.79         (((X13) != (X14)) | ~ (zip_tseitin_0 @ X13 @ X14 @ X15 @ X12))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.60/0.79  thf('8', plain,
% 0.60/0.79      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.60/0.79         ~ (zip_tseitin_0 @ X14 @ X14 @ X15 @ X12)),
% 0.60/0.79      inference('simplify', [status(thm)], ['7'])).
% 0.60/0.79  thf('9', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.60/0.79      inference('sup-', [status(thm)], ['6', '8'])).
% 0.60/0.79  thf(t1_xboole_0, axiom,
% 0.60/0.79    (![A:$i,B:$i,C:$i]:
% 0.60/0.79     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.60/0.79       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.60/0.79  thf('10', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.60/0.79         ((r2_hidden @ X0 @ (k5_xboole_0 @ X1 @ X3))
% 0.60/0.79          | (r2_hidden @ X0 @ X3)
% 0.60/0.79          | ~ (r2_hidden @ X0 @ X1))),
% 0.60/0.79      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.60/0.79  thf('11', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.79         ((r2_hidden @ X0 @ X2)
% 0.60/0.79          | (r2_hidden @ X0 @ (k5_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['9', '10'])).
% 0.60/0.79  thf('12', plain,
% 0.60/0.79      (((r2_hidden @ sk_B @ (k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))
% 0.60/0.79        | (r2_hidden @ sk_B @ (k1_tarski @ sk_A)))),
% 0.60/0.79      inference('sup+', [status(thm)], ['2', '11'])).
% 0.60/0.79  thf(t79_xboole_1, axiom,
% 0.60/0.79    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.60/0.79  thf('13', plain,
% 0.60/0.79      (![X10 : $i, X11 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X11)),
% 0.60/0.79      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.60/0.79  thf(t3_xboole_0, axiom,
% 0.60/0.79    (![A:$i,B:$i]:
% 0.60/0.79     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.60/0.79            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.60/0.79       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.60/0.79            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.60/0.79  thf('14', plain,
% 0.60/0.79      (![X4 : $i, X5 : $i]:
% 0.60/0.79         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C @ X5 @ X4) @ X4))),
% 0.60/0.79      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.60/0.79  thf('15', plain,
% 0.60/0.79      (![X4 : $i, X5 : $i]:
% 0.60/0.79         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C @ X5 @ X4) @ X5))),
% 0.60/0.79      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.60/0.79  thf('16', plain,
% 0.60/0.79      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.60/0.79         (~ (r2_hidden @ X6 @ X4)
% 0.60/0.79          | ~ (r2_hidden @ X6 @ X7)
% 0.60/0.79          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.60/0.79      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.60/0.79  thf('17', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.79         ((r1_xboole_0 @ X1 @ X0)
% 0.60/0.79          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.60/0.79          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.60/0.79      inference('sup-', [status(thm)], ['15', '16'])).
% 0.60/0.79  thf('18', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i]:
% 0.60/0.79         ((r1_xboole_0 @ X0 @ X1)
% 0.60/0.79          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.60/0.79          | (r1_xboole_0 @ X0 @ X1))),
% 0.60/0.79      inference('sup-', [status(thm)], ['14', '17'])).
% 0.60/0.79  thf('19', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i]:
% 0.60/0.79         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.60/0.79      inference('simplify', [status(thm)], ['18'])).
% 0.60/0.79  thf('20', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.60/0.79      inference('sup-', [status(thm)], ['13', '19'])).
% 0.60/0.79  thf('21', plain, ((r2_hidden @ sk_B @ sk_C_1)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('22', plain,
% 0.60/0.79      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.60/0.79         (~ (r2_hidden @ X6 @ X4)
% 0.60/0.79          | ~ (r2_hidden @ X6 @ X7)
% 0.60/0.79          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.60/0.79      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.60/0.79  thf('23', plain,
% 0.60/0.79      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_B @ X0))),
% 0.60/0.79      inference('sup-', [status(thm)], ['21', '22'])).
% 0.60/0.79  thf('24', plain,
% 0.60/0.79      (![X0 : $i]: ~ (r2_hidden @ sk_B @ (k4_xboole_0 @ X0 @ sk_C_1))),
% 0.60/0.79      inference('sup-', [status(thm)], ['20', '23'])).
% 0.60/0.79  thf('25', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 0.60/0.79      inference('clc', [status(thm)], ['12', '24'])).
% 0.60/0.79  thf('26', plain,
% 0.60/0.79      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.60/0.79         ((zip_tseitin_0 @ X13 @ X14 @ X15 @ X16)
% 0.60/0.79          | ((X13) = (X14))
% 0.60/0.79          | ((X13) = (X15))
% 0.60/0.79          | ((X13) = (X16)))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.60/0.79  thf('27', plain,
% 0.60/0.79      (![X4 : $i, X5 : $i]:
% 0.60/0.79         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C @ X5 @ X4) @ X4))),
% 0.60/0.79      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.60/0.79  thf(t69_enumset1, axiom,
% 0.60/0.79    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.60/0.79  thf('28', plain,
% 0.60/0.79      (![X24 : $i]: ((k2_tarski @ X24 @ X24) = (k1_tarski @ X24))),
% 0.60/0.79      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.60/0.79  thf('29', plain,
% 0.60/0.79      (![X25 : $i, X26 : $i]:
% 0.60/0.79         ((k1_enumset1 @ X25 @ X25 @ X26) = (k2_tarski @ X25 @ X26))),
% 0.60/0.79      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.60/0.79  thf('30', plain,
% 0.60/0.79      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.60/0.79         (~ (r2_hidden @ X22 @ X21)
% 0.60/0.79          | ~ (zip_tseitin_0 @ X22 @ X18 @ X19 @ X20)
% 0.60/0.79          | ((X21) != (k1_enumset1 @ X20 @ X19 @ X18)))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.79  thf('31', plain,
% 0.60/0.79      (![X18 : $i, X19 : $i, X20 : $i, X22 : $i]:
% 0.60/0.79         (~ (zip_tseitin_0 @ X22 @ X18 @ X19 @ X20)
% 0.60/0.79          | ~ (r2_hidden @ X22 @ (k1_enumset1 @ X20 @ X19 @ X18)))),
% 0.60/0.79      inference('simplify', [status(thm)], ['30'])).
% 0.60/0.79  thf('32', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.79         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.60/0.79          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.60/0.79      inference('sup-', [status(thm)], ['29', '31'])).
% 0.60/0.79  thf('33', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i]:
% 0.60/0.79         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.60/0.79          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.60/0.79      inference('sup-', [status(thm)], ['28', '32'])).
% 0.60/0.79  thf('34', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i]:
% 0.60/0.79         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.60/0.79          | ~ (zip_tseitin_0 @ (sk_C @ X1 @ (k1_tarski @ X0)) @ X0 @ X0 @ X0))),
% 0.60/0.79      inference('sup-', [status(thm)], ['27', '33'])).
% 0.60/0.79  thf('35', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i]:
% 0.60/0.79         (((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.60/0.79          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.60/0.79          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.60/0.79          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.60/0.79      inference('sup-', [status(thm)], ['26', '34'])).
% 0.60/0.79  thf('36', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i]:
% 0.60/0.79         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.60/0.79          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.60/0.79      inference('simplify', [status(thm)], ['35'])).
% 0.60/0.79  thf('37', plain,
% 0.60/0.79      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.60/0.79         ((zip_tseitin_0 @ X13 @ X14 @ X15 @ X16)
% 0.60/0.79          | ((X13) = (X14))
% 0.60/0.79          | ((X13) = (X15))
% 0.60/0.79          | ((X13) = (X16)))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.60/0.79  thf('38', plain,
% 0.60/0.79      (![X4 : $i, X5 : $i]:
% 0.60/0.79         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C @ X5 @ X4) @ X5))),
% 0.60/0.79      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.60/0.79  thf('39', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i]:
% 0.60/0.79         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.60/0.79          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.60/0.79      inference('sup-', [status(thm)], ['28', '32'])).
% 0.60/0.79  thf('40', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i]:
% 0.60/0.79         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.60/0.79          | ~ (zip_tseitin_0 @ (sk_C @ (k1_tarski @ X0) @ X1) @ X0 @ X0 @ X0))),
% 0.60/0.79      inference('sup-', [status(thm)], ['38', '39'])).
% 0.60/0.79  thf('41', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i]:
% 0.60/0.79         (((sk_C @ (k1_tarski @ X0) @ X1) = (X0))
% 0.60/0.79          | ((sk_C @ (k1_tarski @ X0) @ X1) = (X0))
% 0.60/0.79          | ((sk_C @ (k1_tarski @ X0) @ X1) = (X0))
% 0.60/0.79          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['37', '40'])).
% 0.60/0.79  thf('42', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i]:
% 0.60/0.79         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.60/0.79          | ((sk_C @ (k1_tarski @ X0) @ X1) = (X0)))),
% 0.60/0.79      inference('simplify', [status(thm)], ['41'])).
% 0.60/0.79  thf('43', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i]:
% 0.60/0.79         (((X0) = (X1))
% 0.60/0.79          | (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.60/0.79          | (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.60/0.79      inference('sup+', [status(thm)], ['36', '42'])).
% 0.60/0.79  thf('44', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i]:
% 0.60/0.79         ((r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)) | ((X0) = (X1)))),
% 0.60/0.79      inference('simplify', [status(thm)], ['43'])).
% 0.60/0.79  thf('45', plain,
% 0.60/0.79      (![X24 : $i]: ((k2_tarski @ X24 @ X24) = (k1_tarski @ X24))),
% 0.60/0.79      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.60/0.79  thf('46', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.79         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.60/0.79          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.60/0.79      inference('sup+', [status(thm)], ['3', '5'])).
% 0.60/0.79  thf('47', plain,
% 0.60/0.79      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.60/0.79         (((X13) != (X12)) | ~ (zip_tseitin_0 @ X13 @ X14 @ X15 @ X12))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.60/0.79  thf('48', plain,
% 0.60/0.79      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.60/0.79         ~ (zip_tseitin_0 @ X12 @ X14 @ X15 @ X12)),
% 0.60/0.79      inference('simplify', [status(thm)], ['47'])).
% 0.60/0.79  thf('49', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.60/0.79      inference('sup-', [status(thm)], ['46', '48'])).
% 0.60/0.79  thf('50', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.60/0.79      inference('sup+', [status(thm)], ['45', '49'])).
% 0.60/0.79  thf('51', plain,
% 0.60/0.79      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.60/0.79         (~ (r2_hidden @ X6 @ X4)
% 0.60/0.79          | ~ (r2_hidden @ X6 @ X7)
% 0.60/0.79          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.60/0.79      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.60/0.79  thf('52', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i]:
% 0.60/0.79         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.60/0.79      inference('sup-', [status(thm)], ['50', '51'])).
% 0.60/0.79  thf('53', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i]:
% 0.60/0.79         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.60/0.79      inference('sup-', [status(thm)], ['44', '52'])).
% 0.60/0.79  thf('54', plain, (((sk_B) = (sk_A))),
% 0.60/0.79      inference('sup-', [status(thm)], ['25', '53'])).
% 0.60/0.79  thf('55', plain, (((sk_A) != (sk_B))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('56', plain, ($false),
% 0.60/0.79      inference('simplify_reflect-', [status(thm)], ['54', '55'])).
% 0.60/0.79  
% 0.60/0.79  % SZS output end Refutation
% 0.60/0.79  
% 0.60/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
