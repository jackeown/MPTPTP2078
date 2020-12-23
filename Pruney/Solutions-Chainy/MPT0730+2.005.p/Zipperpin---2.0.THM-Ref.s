%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jxwOH8OzRs

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:43 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 141 expanded)
%              Number of leaves         :   18 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :  555 (1170 expanded)
%              Number of equality atoms :   46 ( 105 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t13_ordinal1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
      <=> ( ( r2_hidden @ A @ B )
          | ( A = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t13_ordinal1])).

thf('0',plain,
    ( ( sk_A != sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_A != sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('2',plain,(
    ! [X70: $i] :
      ( ( k1_ordinal1 @ X70 )
      = ( k2_xboole_0 @ X70 @ ( k1_tarski @ X70 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('3',plain,(
    ! [X18: $i] :
      ( ( k2_tarski @ X18 @ X18 )
      = ( k1_tarski @ X18 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_enumset1 @ X19 @ X19 @ X20 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
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

thf('5',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 )
      | ( r2_hidden @ X11 @ X15 )
      | ( X15
       != ( k1_enumset1 @ X14 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('6',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X11 @ ( k1_enumset1 @ X14 @ X13 @ X12 ) )
      | ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X7 != X6 )
      | ~ ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('9',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ~ ( zip_tseitin_0 @ X6 @ X8 @ X9 @ X6 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','10'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','14'])).

thf('16',plain,
    ( ( sk_A = sk_B )
    | ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
    | ( sk_A != sk_B ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['18'])).

thf('23',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X10 )
      | ( X7 = X8 )
      | ( X7 = X9 )
      | ( X7 = X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('24',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['16'])).

thf('25',plain,(
    ! [X70: $i] :
      ( ( k1_ordinal1 @ X70 )
      = ( k2_xboole_0 @ X70 @ ( k1_tarski @ X70 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('26',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('27',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','28'])).

thf('30',plain,(
    ! [X18: $i] :
      ( ( k2_tarski @ X18 @ X18 )
      = ( k1_tarski @ X18 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('31',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_enumset1 @ X19 @ X19 @ X20 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('32',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ~ ( zip_tseitin_0 @ X16 @ X12 @ X13 @ X14 )
      | ( X15
       != ( k1_enumset1 @ X14 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('33',plain,(
    ! [X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ~ ( zip_tseitin_0 @ X16 @ X12 @ X13 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k1_enumset1 @ X14 @ X13 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','34'])).

thf('36',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ~ ( zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','35'])).

thf('37',plain,
    ( ( ( sk_A = sk_B )
      | ( sk_A = sk_B )
      | ( sk_A = sk_B )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','36'])).

thf('38',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ( sk_A = sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( sk_A != sk_B )
   <= ( sk_A != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,(
    sk_A != sk_B ),
    inference('sat_resolution*',[status(thm)],['1','21'])).

thf('41',plain,(
    sk_A != sk_B ),
    inference(simpl_trail,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['38','41'])).

thf('43',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['18'])).

thf('44',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X70: $i] :
      ( ( k1_ordinal1 @ X70 )
      = ( k2_xboole_0 @ X70 @ ( k1_tarski @ X70 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('46',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['16'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['45','49'])).

thf('51',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['18'])).

thf('52',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
    | ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['16'])).

thf('54',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','21','22','44','52','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jxwOH8OzRs
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:58:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.54  % Solved by: fo/fo7.sh
% 0.36/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.54  % done 210 iterations in 0.096s
% 0.36/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.54  % SZS output start Refutation
% 0.36/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.54  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.36/0.54  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.36/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.36/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.54  thf(t13_ordinal1, conjecture,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.36/0.54       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.36/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.54    (~( ![A:$i,B:$i]:
% 0.36/0.54        ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.36/0.54          ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ) )),
% 0.36/0.54    inference('cnf.neg', [status(esa)], [t13_ordinal1])).
% 0.36/0.54  thf('0', plain,
% 0.36/0.54      ((((sk_A) != (sk_B)) | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('1', plain,
% 0.36/0.54      (~ (((sk_A) = (sk_B))) | ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.36/0.54      inference('split', [status(esa)], ['0'])).
% 0.36/0.54  thf(d1_ordinal1, axiom,
% 0.36/0.54    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.36/0.54  thf('2', plain,
% 0.36/0.54      (![X70 : $i]:
% 0.36/0.54         ((k1_ordinal1 @ X70) = (k2_xboole_0 @ X70 @ (k1_tarski @ X70)))),
% 0.36/0.54      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.36/0.54  thf(t69_enumset1, axiom,
% 0.36/0.54    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.36/0.54  thf('3', plain, (![X18 : $i]: ((k2_tarski @ X18 @ X18) = (k1_tarski @ X18))),
% 0.36/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.54  thf(t70_enumset1, axiom,
% 0.36/0.54    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.36/0.54  thf('4', plain,
% 0.36/0.54      (![X19 : $i, X20 : $i]:
% 0.36/0.54         ((k1_enumset1 @ X19 @ X19 @ X20) = (k2_tarski @ X19 @ X20))),
% 0.36/0.54      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.36/0.54  thf(d1_enumset1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.54     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.36/0.54       ( ![E:$i]:
% 0.36/0.54         ( ( r2_hidden @ E @ D ) <=>
% 0.36/0.54           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.36/0.54  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.36/0.54  thf(zf_stmt_2, axiom,
% 0.36/0.54    (![E:$i,C:$i,B:$i,A:$i]:
% 0.36/0.54     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.36/0.54       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.36/0.54  thf(zf_stmt_3, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.54     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.36/0.54       ( ![E:$i]:
% 0.36/0.54         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.36/0.54  thf('5', plain,
% 0.36/0.54      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.36/0.54         ((zip_tseitin_0 @ X11 @ X12 @ X13 @ X14)
% 0.36/0.54          | (r2_hidden @ X11 @ X15)
% 0.36/0.54          | ((X15) != (k1_enumset1 @ X14 @ X13 @ X12)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.36/0.54  thf('6', plain,
% 0.36/0.54      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.36/0.54         ((r2_hidden @ X11 @ (k1_enumset1 @ X14 @ X13 @ X12))
% 0.36/0.54          | (zip_tseitin_0 @ X11 @ X12 @ X13 @ X14))),
% 0.36/0.54      inference('simplify', [status(thm)], ['5'])).
% 0.36/0.54  thf('7', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.54         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.36/0.54          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.36/0.54      inference('sup+', [status(thm)], ['4', '6'])).
% 0.36/0.54  thf('8', plain,
% 0.36/0.54      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.36/0.54         (((X7) != (X6)) | ~ (zip_tseitin_0 @ X7 @ X8 @ X9 @ X6))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.36/0.54  thf('9', plain,
% 0.36/0.54      (![X6 : $i, X8 : $i, X9 : $i]: ~ (zip_tseitin_0 @ X6 @ X8 @ X9 @ X6)),
% 0.36/0.54      inference('simplify', [status(thm)], ['8'])).
% 0.36/0.54  thf('10', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['7', '9'])).
% 0.36/0.54  thf('11', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.36/0.54      inference('sup+', [status(thm)], ['3', '10'])).
% 0.36/0.54  thf(d3_xboole_0, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.36/0.54       ( ![D:$i]:
% 0.36/0.54         ( ( r2_hidden @ D @ C ) <=>
% 0.36/0.54           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.36/0.54  thf('12', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X0 @ X1)
% 0.36/0.54          | (r2_hidden @ X0 @ X2)
% 0.36/0.54          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.36/0.54      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.36/0.54  thf('13', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.36/0.54         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.36/0.54      inference('simplify', [status(thm)], ['12'])).
% 0.36/0.54  thf('14', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['11', '13'])).
% 0.36/0.54  thf('15', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_ordinal1 @ X0))),
% 0.36/0.54      inference('sup+', [status(thm)], ['2', '14'])).
% 0.36/0.54  thf('16', plain,
% 0.36/0.54      ((((sk_A) = (sk_B))
% 0.36/0.54        | (r2_hidden @ sk_A @ sk_B)
% 0.36/0.54        | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('17', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 0.36/0.54      inference('split', [status(esa)], ['16'])).
% 0.36/0.54  thf('18', plain,
% 0.36/0.54      ((~ (r2_hidden @ sk_A @ sk_B)
% 0.36/0.54        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('19', plain,
% 0.36/0.54      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.36/0.54         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.36/0.54      inference('split', [status(esa)], ['18'])).
% 0.36/0.54  thf('20', plain,
% 0.36/0.54      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 0.36/0.54         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.36/0.54             (((sk_A) = (sk_B))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['17', '19'])).
% 0.36/0.54  thf('21', plain,
% 0.36/0.54      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) | ~ (((sk_A) = (sk_B)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['15', '20'])).
% 0.36/0.54  thf('22', plain,
% 0.36/0.54      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.36/0.54       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.36/0.54      inference('split', [status(esa)], ['18'])).
% 0.36/0.54  thf('23', plain,
% 0.36/0.54      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.36/0.54         ((zip_tseitin_0 @ X7 @ X8 @ X9 @ X10)
% 0.36/0.54          | ((X7) = (X8))
% 0.36/0.54          | ((X7) = (X9))
% 0.36/0.54          | ((X7) = (X10)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.36/0.54  thf('24', plain,
% 0.36/0.54      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.36/0.54         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.36/0.54      inference('split', [status(esa)], ['16'])).
% 0.36/0.54  thf('25', plain,
% 0.36/0.54      (![X70 : $i]:
% 0.36/0.54         ((k1_ordinal1 @ X70) = (k2_xboole_0 @ X70 @ (k1_tarski @ X70)))),
% 0.36/0.54      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.36/0.54  thf('26', plain,
% 0.36/0.54      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X4 @ X2)
% 0.36/0.54          | (r2_hidden @ X4 @ X3)
% 0.36/0.54          | (r2_hidden @ X4 @ X1)
% 0.36/0.54          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.36/0.54      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.36/0.54  thf('27', plain,
% 0.36/0.54      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.36/0.54         ((r2_hidden @ X4 @ X1)
% 0.36/0.54          | (r2_hidden @ X4 @ X3)
% 0.36/0.54          | ~ (r2_hidden @ X4 @ (k2_xboole_0 @ X3 @ X1)))),
% 0.36/0.54      inference('simplify', [status(thm)], ['26'])).
% 0.36/0.54  thf('28', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.36/0.54          | (r2_hidden @ X1 @ X0)
% 0.36/0.54          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['25', '27'])).
% 0.36/0.54  thf('29', plain,
% 0.36/0.54      ((((r2_hidden @ sk_A @ (k1_tarski @ sk_B)) | (r2_hidden @ sk_A @ sk_B)))
% 0.36/0.54         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['24', '28'])).
% 0.36/0.54  thf('30', plain,
% 0.36/0.54      (![X18 : $i]: ((k2_tarski @ X18 @ X18) = (k1_tarski @ X18))),
% 0.36/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.54  thf('31', plain,
% 0.36/0.54      (![X19 : $i, X20 : $i]:
% 0.36/0.54         ((k1_enumset1 @ X19 @ X19 @ X20) = (k2_tarski @ X19 @ X20))),
% 0.36/0.54      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.36/0.54  thf('32', plain,
% 0.36/0.54      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X16 @ X15)
% 0.36/0.54          | ~ (zip_tseitin_0 @ X16 @ X12 @ X13 @ X14)
% 0.36/0.54          | ((X15) != (k1_enumset1 @ X14 @ X13 @ X12)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.36/0.54  thf('33', plain,
% 0.36/0.54      (![X12 : $i, X13 : $i, X14 : $i, X16 : $i]:
% 0.36/0.54         (~ (zip_tseitin_0 @ X16 @ X12 @ X13 @ X14)
% 0.36/0.54          | ~ (r2_hidden @ X16 @ (k1_enumset1 @ X14 @ X13 @ X12)))),
% 0.36/0.54      inference('simplify', [status(thm)], ['32'])).
% 0.36/0.54  thf('34', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.36/0.54          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['31', '33'])).
% 0.36/0.54  thf('35', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.36/0.54          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['30', '34'])).
% 0.36/0.54  thf('36', plain,
% 0.36/0.54      ((((r2_hidden @ sk_A @ sk_B)
% 0.36/0.54         | ~ (zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B)))
% 0.36/0.54         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['29', '35'])).
% 0.36/0.54  thf('37', plain,
% 0.36/0.54      (((((sk_A) = (sk_B))
% 0.36/0.54         | ((sk_A) = (sk_B))
% 0.36/0.54         | ((sk_A) = (sk_B))
% 0.36/0.54         | (r2_hidden @ sk_A @ sk_B)))
% 0.36/0.54         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['23', '36'])).
% 0.36/0.54  thf('38', plain,
% 0.36/0.54      ((((r2_hidden @ sk_A @ sk_B) | ((sk_A) = (sk_B))))
% 0.36/0.54         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.36/0.54      inference('simplify', [status(thm)], ['37'])).
% 0.36/0.54  thf('39', plain, ((((sk_A) != (sk_B))) <= (~ (((sk_A) = (sk_B))))),
% 0.36/0.54      inference('split', [status(esa)], ['0'])).
% 0.36/0.54  thf('40', plain, (~ (((sk_A) = (sk_B)))),
% 0.36/0.54      inference('sat_resolution*', [status(thm)], ['1', '21'])).
% 0.36/0.54  thf('41', plain, (((sk_A) != (sk_B))),
% 0.36/0.54      inference('simpl_trail', [status(thm)], ['39', '40'])).
% 0.36/0.54  thf('42', plain,
% 0.36/0.54      (((r2_hidden @ sk_A @ sk_B))
% 0.36/0.54         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.36/0.54      inference('simplify_reflect-', [status(thm)], ['38', '41'])).
% 0.36/0.54  thf('43', plain,
% 0.36/0.54      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.36/0.54      inference('split', [status(esa)], ['18'])).
% 0.36/0.54  thf('44', plain,
% 0.36/0.54      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.36/0.54       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['42', '43'])).
% 0.36/0.54  thf('45', plain,
% 0.36/0.54      (![X70 : $i]:
% 0.36/0.54         ((k1_ordinal1 @ X70) = (k2_xboole_0 @ X70 @ (k1_tarski @ X70)))),
% 0.36/0.54      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.36/0.54  thf('46', plain,
% 0.36/0.54      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.36/0.54      inference('split', [status(esa)], ['16'])).
% 0.36/0.54  thf('47', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X0 @ X3)
% 0.36/0.54          | (r2_hidden @ X0 @ X2)
% 0.36/0.54          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.36/0.54      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.36/0.54  thf('48', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.36/0.54         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 0.36/0.54      inference('simplify', [status(thm)], ['47'])).
% 0.36/0.54  thf('49', plain,
% 0.36/0.54      ((![X0 : $i]: (r2_hidden @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))
% 0.36/0.54         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['46', '48'])).
% 0.36/0.54  thf('50', plain,
% 0.36/0.54      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.36/0.54         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.36/0.54      inference('sup+', [status(thm)], ['45', '49'])).
% 0.36/0.54  thf('51', plain,
% 0.36/0.54      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.36/0.54         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.36/0.54      inference('split', [status(esa)], ['18'])).
% 0.36/0.54  thf('52', plain,
% 0.36/0.54      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.36/0.54       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['50', '51'])).
% 0.36/0.54  thf('53', plain,
% 0.36/0.54      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.36/0.54       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) | (((sk_A) = (sk_B)))),
% 0.36/0.54      inference('split', [status(esa)], ['16'])).
% 0.36/0.54  thf('54', plain, ($false),
% 0.36/0.54      inference('sat_resolution*', [status(thm)],
% 0.36/0.54                ['1', '21', '22', '44', '52', '53'])).
% 0.36/0.54  
% 0.36/0.54  % SZS output end Refutation
% 0.36/0.54  
% 0.38/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
