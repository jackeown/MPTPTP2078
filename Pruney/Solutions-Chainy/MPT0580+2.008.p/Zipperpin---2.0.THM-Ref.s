%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uuspheJnL7

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 104 expanded)
%              Number of leaves         :   22 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  557 ( 858 expanded)
%              Number of equality atoms :   45 (  73 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(v3_relat_1_type,type,(
    v3_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t184_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v3_relat_1 @ A )
      <=> ! [B: $i] :
            ( ( r2_hidden @ B @ ( k2_relat_1 @ A ) )
           => ( B = k1_xboole_0 ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( v3_relat_1 @ A )
        <=> ! [B: $i] :
              ( ( r2_hidden @ B @ ( k2_relat_1 @ A ) )
             => ( B = k1_xboole_0 ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t184_relat_1])).

thf('0',plain,
    ( ( sk_B != k1_xboole_0 )
    | ~ ( v3_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_B != k1_xboole_0 )
    | ~ ( v3_relat_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) )
    | ~ ( v3_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) )
    | ~ ( v3_relat_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 )
      | ( X5 = X6 )
      | ( X5 = X7 )
      | ( X5 = X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('5',plain,(
    ! [X20: $i] :
      ( ~ ( r2_hidden @ X20 @ ( k2_relat_1 @ sk_A ) )
      | ( X20 = k1_xboole_0 )
      | ( v3_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v3_relat_1 @ sk_A )
   <= ( v3_relat_1 @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) )
   <= ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf(d15_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v3_relat_1 @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_tarski @ k1_xboole_0 ) ) ) ) )).

thf('8',plain,(
    ! [X19: $i] :
      ( ~ ( v3_relat_1 @ X19 )
      | ( r1_tarski @ ( k2_relat_1 @ X19 ) @ ( k1_tarski @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d15_relat_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v3_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
      | ~ ( v3_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
      | ~ ( v3_relat_1 @ sk_A ) )
   <= ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
   <= ( ( v3_relat_1 @ sk_A )
      & ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('15',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X17 @ X17 @ X18 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
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

thf('17',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( zip_tseitin_0 @ X14 @ X10 @ X11 @ X12 )
      | ( X13
       != ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('18',plain,(
    ! [X10: $i,X11: $i,X12: $i,X14: $i] :
      ( ~ ( zip_tseitin_0 @ X14 @ X10 @ X11 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','19'])).

thf('21',plain,
    ( ~ ( zip_tseitin_0 @ sk_B @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
   <= ( ( v3_relat_1 @ sk_A )
      & ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( v3_relat_1 @ sk_A )
      & ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','21'])).

thf('23',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ( v3_relat_1 @ sk_A )
      & ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('25',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( v3_relat_1 @ sk_A )
      & ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) )
    | ~ ( v3_relat_1 @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ! [X20: $i] :
        ( ( X20 = k1_xboole_0 )
        | ~ ( r2_hidden @ X20 @ ( k2_relat_1 @ sk_A ) ) )
    | ( v3_relat_1 @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('28',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('29',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X17 @ X17 @ X18 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('30',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( r2_hidden @ X9 @ X13 )
      | ( X13
       != ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('31',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X9 @ ( k1_enumset1 @ X12 @ X11 @ X10 ) )
      | ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','31'])).

thf('33',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X5 != X4 )
      | ~ ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('34',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ~ ( zip_tseitin_0 @ X4 @ X6 @ X7 @ X4 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','35'])).

thf('37',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('38',plain,
    ( ! [X20: $i] :
        ( ( X20 = k1_xboole_0 )
        | ~ ( r2_hidden @ X20 @ ( k2_relat_1 @ sk_A ) ) )
   <= ! [X20: $i] :
        ( ( X20 = k1_xboole_0 )
        | ~ ( r2_hidden @ X20 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['5'])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
        | ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_A ) )
          = k1_xboole_0 ) )
   <= ! [X20: $i] :
        ( ( X20 = k1_xboole_0 )
        | ~ ( r2_hidden @ X20 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('41',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ k1_xboole_0 @ X0 )
        | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
        | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 ) )
   <= ! [X20: $i] :
        ( ( X20 = k1_xboole_0 )
        | ~ ( r2_hidden @ X20 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ k1_xboole_0 @ X0 ) )
   <= ! [X20: $i] :
        ( ( X20 = k1_xboole_0 )
        | ~ ( r2_hidden @ X20 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k1_tarski @ k1_xboole_0 ) )
   <= ! [X20: $i] :
        ( ( X20 = k1_xboole_0 )
        | ~ ( r2_hidden @ X20 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','42'])).

thf('44',plain,(
    ! [X19: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X19 ) @ ( k1_tarski @ k1_xboole_0 ) )
      | ( v3_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d15_relat_1])).

thf('45',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( v3_relat_1 @ sk_A ) )
   <= ! [X20: $i] :
        ( ( X20 = k1_xboole_0 )
        | ~ ( r2_hidden @ X20 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v3_relat_1 @ sk_A )
   <= ! [X20: $i] :
        ( ( X20 = k1_xboole_0 )
        | ~ ( r2_hidden @ X20 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( v3_relat_1 @ sk_A )
   <= ~ ( v3_relat_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('49',plain,
    ( ~ ! [X20: $i] :
          ( ( X20 = k1_xboole_0 )
          | ~ ( r2_hidden @ X20 @ ( k2_relat_1 @ sk_A ) ) )
    | ( v3_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','26','27','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uuspheJnL7
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:36:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 60 iterations in 0.021s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.47  thf(v3_relat_1_type, type, v3_relat_1: $i > $o).
% 0.20/0.47  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.47  thf(t184_relat_1, conjecture,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ A ) =>
% 0.20/0.47       ( ( v3_relat_1 @ A ) <=>
% 0.20/0.47         ( ![B:$i]:
% 0.20/0.47           ( ( r2_hidden @ B @ ( k2_relat_1 @ A ) ) =>
% 0.20/0.47             ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i]:
% 0.20/0.47        ( ( v1_relat_1 @ A ) =>
% 0.20/0.47          ( ( v3_relat_1 @ A ) <=>
% 0.20/0.47            ( ![B:$i]:
% 0.20/0.47              ( ( r2_hidden @ B @ ( k2_relat_1 @ A ) ) =>
% 0.20/0.47                ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t184_relat_1])).
% 0.20/0.47  thf('0', plain, ((((sk_B) != (k1_xboole_0)) | ~ (v3_relat_1 @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('1', plain, (~ (((sk_B) = (k1_xboole_0))) | ~ ((v3_relat_1 @ sk_A))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A)) | ~ (v3_relat_1 @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))) | ~ ((v3_relat_1 @ sk_A))),
% 0.20/0.47      inference('split', [status(esa)], ['2'])).
% 0.20/0.47  thf(d1_enumset1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.47     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.47       ( ![E:$i]:
% 0.20/0.47         ( ( r2_hidden @ E @ D ) <=>
% 0.20/0.47           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_1, axiom,
% 0.20/0.47    (![E:$i,C:$i,B:$i,A:$i]:
% 0.20/0.47     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.20/0.47       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.47         ((zip_tseitin_0 @ X5 @ X6 @ X7 @ X8)
% 0.20/0.47          | ((X5) = (X6))
% 0.20/0.47          | ((X5) = (X7))
% 0.20/0.47          | ((X5) = (X8)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X20 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X20 @ (k2_relat_1 @ sk_A))
% 0.20/0.47          | ((X20) = (k1_xboole_0))
% 0.20/0.47          | (v3_relat_1 @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('6', plain, (((v3_relat_1 @ sk_A)) <= (((v3_relat_1 @ sk_A)))),
% 0.20/0.47      inference('split', [status(esa)], ['5'])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A)))
% 0.20/0.47         <= (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.20/0.47      inference('split', [status(esa)], ['2'])).
% 0.20/0.47  thf(d15_relat_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ A ) =>
% 0.20/0.47       ( ( v3_relat_1 @ A ) <=>
% 0.20/0.47         ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_tarski @ k1_xboole_0 ) ) ) ))).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X19 : $i]:
% 0.20/0.47         (~ (v3_relat_1 @ X19)
% 0.20/0.47          | (r1_tarski @ (k2_relat_1 @ X19) @ (k1_tarski @ k1_xboole_0))
% 0.20/0.47          | ~ (v1_relat_1 @ X19))),
% 0.20/0.47      inference('cnf', [status(esa)], [d15_relat_1])).
% 0.20/0.47  thf(d3_tarski, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.47          | (r2_hidden @ X0 @ X2)
% 0.20/0.47          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X0)
% 0.20/0.47          | ~ (v3_relat_1 @ X0)
% 0.20/0.47          | (r2_hidden @ X1 @ (k1_tarski @ k1_xboole_0))
% 0.20/0.47          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      ((((r2_hidden @ sk_B @ (k1_tarski @ k1_xboole_0))
% 0.20/0.47         | ~ (v3_relat_1 @ sk_A)
% 0.20/0.47         | ~ (v1_relat_1 @ sk_A)))
% 0.20/0.47         <= (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['7', '10'])).
% 0.20/0.47  thf('12', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      ((((r2_hidden @ sk_B @ (k1_tarski @ k1_xboole_0)) | ~ (v3_relat_1 @ sk_A)))
% 0.20/0.47         <= (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.20/0.47      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (((r2_hidden @ sk_B @ (k1_tarski @ k1_xboole_0)))
% 0.20/0.47         <= (((v3_relat_1 @ sk_A)) & ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['6', '13'])).
% 0.20/0.47  thf(t69_enumset1, axiom,
% 0.20/0.47    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.20/0.47      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.47  thf(t70_enumset1, axiom,
% 0.20/0.47    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      (![X17 : $i, X18 : $i]:
% 0.20/0.47         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 0.20/0.47      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.47  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.20/0.47  thf(zf_stmt_3, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.47     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.47       ( ![E:$i]:
% 0.20/0.47         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X14 @ X13)
% 0.20/0.47          | ~ (zip_tseitin_0 @ X14 @ X10 @ X11 @ X12)
% 0.20/0.47          | ((X13) != (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      (![X10 : $i, X11 : $i, X12 : $i, X14 : $i]:
% 0.20/0.47         (~ (zip_tseitin_0 @ X14 @ X10 @ X11 @ X12)
% 0.20/0.47          | ~ (r2_hidden @ X14 @ (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.20/0.47          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['16', '18'])).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.20/0.47          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['15', '19'])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      ((~ (zip_tseitin_0 @ sk_B @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))
% 0.20/0.47         <= (((v3_relat_1 @ sk_A)) & ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['14', '20'])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      (((((sk_B) = (k1_xboole_0))
% 0.20/0.47         | ((sk_B) = (k1_xboole_0))
% 0.20/0.47         | ((sk_B) = (k1_xboole_0))))
% 0.20/0.47         <= (((v3_relat_1 @ sk_A)) & ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['4', '21'])).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      ((((sk_B) = (k1_xboole_0)))
% 0.20/0.47         <= (((v3_relat_1 @ sk_A)) & ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.20/0.47      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.47  thf('24', plain,
% 0.20/0.47      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf('25', plain,
% 0.20/0.47      ((((sk_B) != (sk_B)))
% 0.20/0.47         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 0.20/0.47             ((v3_relat_1 @ sk_A)) & 
% 0.20/0.47             ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.47  thf('26', plain,
% 0.20/0.47      (~ ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))) | 
% 0.20/0.47       ~ ((v3_relat_1 @ sk_A)) | (((sk_B) = (k1_xboole_0)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      ((![X20 : $i]:
% 0.20/0.47          (((X20) = (k1_xboole_0)) | ~ (r2_hidden @ X20 @ (k2_relat_1 @ sk_A)))) | 
% 0.20/0.47       ((v3_relat_1 @ sk_A))),
% 0.20/0.47      inference('split', [status(esa)], ['5'])).
% 0.20/0.47  thf('28', plain,
% 0.20/0.47      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.20/0.47      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.47  thf('29', plain,
% 0.20/0.47      (![X17 : $i, X18 : $i]:
% 0.20/0.47         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 0.20/0.47      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.47  thf('30', plain,
% 0.20/0.47      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.47         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 0.20/0.47          | (r2_hidden @ X9 @ X13)
% 0.20/0.47          | ((X13) != (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.47  thf('31', plain,
% 0.20/0.47      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.47         ((r2_hidden @ X9 @ (k1_enumset1 @ X12 @ X11 @ X10))
% 0.20/0.47          | (zip_tseitin_0 @ X9 @ X10 @ X11 @ X12))),
% 0.20/0.47      inference('simplify', [status(thm)], ['30'])).
% 0.20/0.47  thf('32', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.20/0.47          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.20/0.47      inference('sup+', [status(thm)], ['29', '31'])).
% 0.20/0.47  thf('33', plain,
% 0.20/0.47      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.47         (((X5) != (X4)) | ~ (zip_tseitin_0 @ X5 @ X6 @ X7 @ X4))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.47  thf('34', plain,
% 0.20/0.47      (![X4 : $i, X6 : $i, X7 : $i]: ~ (zip_tseitin_0 @ X4 @ X6 @ X7 @ X4)),
% 0.20/0.47      inference('simplify', [status(thm)], ['33'])).
% 0.20/0.47  thf('35', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['32', '34'])).
% 0.20/0.47  thf('36', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.47      inference('sup+', [status(thm)], ['28', '35'])).
% 0.20/0.47  thf('37', plain,
% 0.20/0.47      (![X1 : $i, X3 : $i]:
% 0.20/0.47         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.47      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.47  thf('38', plain,
% 0.20/0.47      ((![X20 : $i]:
% 0.20/0.47          (((X20) = (k1_xboole_0)) | ~ (r2_hidden @ X20 @ (k2_relat_1 @ sk_A))))
% 0.20/0.47         <= ((![X20 : $i]:
% 0.20/0.47                (((X20) = (k1_xboole_0))
% 0.20/0.47                 | ~ (r2_hidden @ X20 @ (k2_relat_1 @ sk_A)))))),
% 0.20/0.47      inference('split', [status(esa)], ['5'])).
% 0.20/0.47  thf('39', plain,
% 0.20/0.47      ((![X0 : $i]:
% 0.20/0.47          ((r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 0.20/0.47           | ((sk_C @ X0 @ (k2_relat_1 @ sk_A)) = (k1_xboole_0))))
% 0.20/0.47         <= ((![X20 : $i]:
% 0.20/0.47                (((X20) = (k1_xboole_0))
% 0.20/0.47                 | ~ (r2_hidden @ X20 @ (k2_relat_1 @ sk_A)))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.47  thf('40', plain,
% 0.20/0.47      (![X1 : $i, X3 : $i]:
% 0.20/0.47         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.47      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.47  thf('41', plain,
% 0.20/0.47      ((![X0 : $i]:
% 0.20/0.47          (~ (r2_hidden @ k1_xboole_0 @ X0)
% 0.20/0.47           | (r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 0.20/0.47           | (r1_tarski @ (k2_relat_1 @ sk_A) @ X0)))
% 0.20/0.47         <= ((![X20 : $i]:
% 0.20/0.47                (((X20) = (k1_xboole_0))
% 0.20/0.47                 | ~ (r2_hidden @ X20 @ (k2_relat_1 @ sk_A)))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.47  thf('42', plain,
% 0.20/0.47      ((![X0 : $i]:
% 0.20/0.47          ((r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 0.20/0.47           | ~ (r2_hidden @ k1_xboole_0 @ X0)))
% 0.20/0.47         <= ((![X20 : $i]:
% 0.20/0.47                (((X20) = (k1_xboole_0))
% 0.20/0.47                 | ~ (r2_hidden @ X20 @ (k2_relat_1 @ sk_A)))))),
% 0.20/0.47      inference('simplify', [status(thm)], ['41'])).
% 0.20/0.47  thf('43', plain,
% 0.20/0.47      (((r1_tarski @ (k2_relat_1 @ sk_A) @ (k1_tarski @ k1_xboole_0)))
% 0.20/0.47         <= ((![X20 : $i]:
% 0.20/0.47                (((X20) = (k1_xboole_0))
% 0.20/0.47                 | ~ (r2_hidden @ X20 @ (k2_relat_1 @ sk_A)))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['36', '42'])).
% 0.20/0.47  thf('44', plain,
% 0.20/0.47      (![X19 : $i]:
% 0.20/0.47         (~ (r1_tarski @ (k2_relat_1 @ X19) @ (k1_tarski @ k1_xboole_0))
% 0.20/0.47          | (v3_relat_1 @ X19)
% 0.20/0.47          | ~ (v1_relat_1 @ X19))),
% 0.20/0.47      inference('cnf', [status(esa)], [d15_relat_1])).
% 0.20/0.47  thf('45', plain,
% 0.20/0.47      (((~ (v1_relat_1 @ sk_A) | (v3_relat_1 @ sk_A)))
% 0.20/0.47         <= ((![X20 : $i]:
% 0.20/0.47                (((X20) = (k1_xboole_0))
% 0.20/0.47                 | ~ (r2_hidden @ X20 @ (k2_relat_1 @ sk_A)))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.47  thf('46', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('47', plain,
% 0.20/0.47      (((v3_relat_1 @ sk_A))
% 0.20/0.47         <= ((![X20 : $i]:
% 0.20/0.47                (((X20) = (k1_xboole_0))
% 0.20/0.47                 | ~ (r2_hidden @ X20 @ (k2_relat_1 @ sk_A)))))),
% 0.20/0.47      inference('demod', [status(thm)], ['45', '46'])).
% 0.20/0.47  thf('48', plain, ((~ (v3_relat_1 @ sk_A)) <= (~ ((v3_relat_1 @ sk_A)))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf('49', plain,
% 0.20/0.47      (~
% 0.20/0.47       (![X20 : $i]:
% 0.20/0.47          (((X20) = (k1_xboole_0)) | ~ (r2_hidden @ X20 @ (k2_relat_1 @ sk_A)))) | 
% 0.20/0.47       ((v3_relat_1 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.47  thf('50', plain, ($false),
% 0.20/0.47      inference('sat_resolution*', [status(thm)], ['1', '3', '26', '27', '49'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
