%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4zLDp3v8Cb

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:05 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 129 expanded)
%              Number of leaves         :   16 (  40 expanded)
%              Depth                    :   14
%              Number of atoms          :  572 (1236 expanded)
%              Number of equality atoms :   97 ( 202 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_tarski @ C @ D ) ) ) ) ) )).

thf('0',plain,(
    ! [X20: $i] :
      ( ( X20 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X20 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ( X10 = X9 )
      | ( X10 = X6 )
      | ( X8
       != ( k2_tarski @ X9 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('2',plain,(
    ! [X6: $i,X9: $i,X10: $i] :
      ( ( X10 = X6 )
      | ( X10 = X9 )
      | ~ ( r2_hidden @ X10 @ ( k2_tarski @ X9 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_tarski @ X1 @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k2_tarski @ X1 @ X0 ) )
        = X1 )
      | ( ( sk_B @ ( k2_tarski @ X1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X1 )
      | ( ( sk_B @ ( k2_tarski @ X0 @ X1 ) )
        = X1 )
      | ( ( k2_tarski @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(eq_fact,[status(thm)],['3'])).

thf('5',plain,(
    ! [X1: $i] :
      ( ( ( k2_tarski @ X1 @ X1 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k2_tarski @ X1 @ X1 ) )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X7 != X6 )
      | ( r2_hidden @ X7 @ X8 )
      | ( X8
       != ( k2_tarski @ X9 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('7',plain,(
    ! [X6: $i,X9: $i] :
      ( r2_hidden @ X6 @ ( k2_tarski @ X9 @ X6 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t20_mcart_1,conjecture,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ? [B: $i,C: $i] :
            ( A
            = ( k4_tarski @ B @ C ) )
       => ( ( A
           != ( k1_mcart_1 @ A ) )
          & ( A
           != ( k2_mcart_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_mcart_1])).

thf('8',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('9',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X17 @ X18 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('10',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,
    ( ( sk_A = sk_B_1 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['10','12'])).

thf('14',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( X20 = k1_xboole_0 )
      | ~ ( r2_hidden @ X22 @ X20 )
      | ( ( sk_B @ X20 )
       != ( k4_tarski @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_A )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ! [X0: $i] :
        ( ( ( k2_tarski @ X0 @ sk_A )
          = k1_xboole_0 )
        | ( ( sk_B @ ( k2_tarski @ X0 @ sk_A ) )
         != sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','17'])).

thf('19',plain,
    ( ( ( sk_A != sk_A )
      | ( ( k2_tarski @ sk_A @ sk_A )
        = k1_xboole_0 )
      | ( ( k2_tarski @ sk_A @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','18'])).

thf('20',plain,
    ( ( ( k2_tarski @ sk_A @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X6: $i,X9: $i] :
      ( r2_hidden @ X6 @ ( k2_tarski @ X9 @ X6 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('22',plain,
    ( ( r2_hidden @ sk_A @ k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X1: $i] :
      ( ( ( k2_tarski @ X1 @ X1 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k2_tarski @ X1 @ X1 ) )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('24',plain,(
    ! [X6: $i,X9: $i] :
      ( r2_hidden @ X6 @ ( k2_tarski @ X9 @ X6 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('25',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X17: $i,X19: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X17 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('27',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['11'])).

thf('29',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( X20 = k1_xboole_0 )
      | ~ ( r2_hidden @ X21 @ X20 )
      | ( ( sk_B @ X20 )
       != ( k4_tarski @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('33',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_A )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ( ( k2_tarski @ X0 @ sk_A )
          = k1_xboole_0 )
        | ( ( sk_B @ ( k2_tarski @ X0 @ sk_A ) )
         != sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','33'])).

thf('35',plain,
    ( ( ( sk_A != sk_A )
      | ( ( k2_tarski @ sk_A @ sk_A )
        = k1_xboole_0 )
      | ( ( k2_tarski @ sk_A @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','34'])).

thf('36',plain,
    ( ( ( k2_tarski @ sk_A @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X6: $i,X9: $i] :
      ( r2_hidden @ X6 @ ( k2_tarski @ X9 @ X6 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('38',plain,
    ( ( r2_hidden @ sk_A @ k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X20: $i] :
      ( ( X20 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X20 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('40',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('41',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X20: $i] :
      ( ( X20 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X20 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('44',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('45',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['50'])).

thf('52',plain,(
    sk_A
 != ( k2_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','51'])).

thf('53',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['11'])).

thf('54',plain,
    ( sk_A
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['52','53'])).

thf('55',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['22','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['50'])).

thf('57',plain,(
    $false ),
    inference('sup-',[status(thm)],['55','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4zLDp3v8Cb
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:07:10 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.38/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.59  % Solved by: fo/fo7.sh
% 0.38/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.59  % done 210 iterations in 0.138s
% 0.38/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.59  % SZS output start Refutation
% 0.38/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.59  thf(sk_B_type, type, sk_B: $i > $i).
% 0.38/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.59  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.38/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.59  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.38/0.59  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.38/0.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.38/0.59  thf(t9_mcart_1, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.38/0.59          ( ![B:$i]:
% 0.38/0.59            ( ~( ( r2_hidden @ B @ A ) & 
% 0.38/0.59                 ( ![C:$i,D:$i]:
% 0.38/0.59                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.38/0.59                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.59  thf('0', plain,
% 0.38/0.59      (![X20 : $i]:
% 0.38/0.59         (((X20) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X20) @ X20))),
% 0.38/0.59      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.38/0.59  thf(d2_tarski, axiom,
% 0.38/0.59    (![A:$i,B:$i,C:$i]:
% 0.38/0.59     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.38/0.59       ( ![D:$i]:
% 0.38/0.59         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.38/0.59  thf('1', plain,
% 0.38/0.59      (![X6 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.38/0.59         (~ (r2_hidden @ X10 @ X8)
% 0.38/0.59          | ((X10) = (X9))
% 0.38/0.59          | ((X10) = (X6))
% 0.38/0.59          | ((X8) != (k2_tarski @ X9 @ X6)))),
% 0.38/0.59      inference('cnf', [status(esa)], [d2_tarski])).
% 0.38/0.59  thf('2', plain,
% 0.38/0.59      (![X6 : $i, X9 : $i, X10 : $i]:
% 0.38/0.59         (((X10) = (X6))
% 0.38/0.59          | ((X10) = (X9))
% 0.38/0.59          | ~ (r2_hidden @ X10 @ (k2_tarski @ X9 @ X6)))),
% 0.38/0.59      inference('simplify', [status(thm)], ['1'])).
% 0.38/0.59  thf('3', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (((k2_tarski @ X1 @ X0) = (k1_xboole_0))
% 0.38/0.59          | ((sk_B @ (k2_tarski @ X1 @ X0)) = (X1))
% 0.38/0.59          | ((sk_B @ (k2_tarski @ X1 @ X0)) = (X0)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['0', '2'])).
% 0.38/0.59  thf('4', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (((X0) != (X1))
% 0.38/0.59          | ((sk_B @ (k2_tarski @ X0 @ X1)) = (X1))
% 0.38/0.59          | ((k2_tarski @ X0 @ X1) = (k1_xboole_0)))),
% 0.38/0.59      inference('eq_fact', [status(thm)], ['3'])).
% 0.38/0.59  thf('5', plain,
% 0.38/0.59      (![X1 : $i]:
% 0.38/0.59         (((k2_tarski @ X1 @ X1) = (k1_xboole_0))
% 0.38/0.59          | ((sk_B @ (k2_tarski @ X1 @ X1)) = (X1)))),
% 0.38/0.59      inference('simplify', [status(thm)], ['4'])).
% 0.38/0.59  thf('6', plain,
% 0.38/0.59      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.38/0.59         (((X7) != (X6))
% 0.38/0.59          | (r2_hidden @ X7 @ X8)
% 0.38/0.59          | ((X8) != (k2_tarski @ X9 @ X6)))),
% 0.38/0.59      inference('cnf', [status(esa)], [d2_tarski])).
% 0.38/0.59  thf('7', plain,
% 0.38/0.59      (![X6 : $i, X9 : $i]: (r2_hidden @ X6 @ (k2_tarski @ X9 @ X6))),
% 0.38/0.59      inference('simplify', [status(thm)], ['6'])).
% 0.38/0.59  thf(t20_mcart_1, conjecture,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.38/0.59       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.38/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.59    (~( ![A:$i]:
% 0.38/0.59        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.38/0.59          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.38/0.59    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.38/0.59  thf('8', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(t7_mcart_1, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.38/0.59       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.38/0.59  thf('9', plain,
% 0.38/0.59      (![X17 : $i, X18 : $i]: ((k1_mcart_1 @ (k4_tarski @ X17 @ X18)) = (X17))),
% 0.38/0.59      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.38/0.59  thf('10', plain, (((k1_mcart_1 @ sk_A) = (sk_B_1))),
% 0.38/0.59      inference('sup+', [status(thm)], ['8', '9'])).
% 0.38/0.59  thf('11', plain,
% 0.38/0.59      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('12', plain,
% 0.38/0.59      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.38/0.59      inference('split', [status(esa)], ['11'])).
% 0.38/0.59  thf('13', plain,
% 0.38/0.59      ((((sk_A) = (sk_B_1))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.38/0.59      inference('sup+', [status(thm)], ['10', '12'])).
% 0.38/0.59  thf('14', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('15', plain,
% 0.38/0.59      ((((sk_A) = (k4_tarski @ sk_A @ sk_C)))
% 0.38/0.59         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.38/0.59      inference('sup+', [status(thm)], ['13', '14'])).
% 0.38/0.59  thf('16', plain,
% 0.38/0.59      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.38/0.59         (((X20) = (k1_xboole_0))
% 0.38/0.59          | ~ (r2_hidden @ X22 @ X20)
% 0.38/0.59          | ((sk_B @ X20) != (k4_tarski @ X22 @ X21)))),
% 0.38/0.59      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.38/0.59  thf('17', plain,
% 0.38/0.59      ((![X0 : $i]:
% 0.38/0.59          (((sk_B @ X0) != (sk_A))
% 0.38/0.59           | ~ (r2_hidden @ sk_A @ X0)
% 0.38/0.59           | ((X0) = (k1_xboole_0))))
% 0.38/0.59         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.38/0.59      inference('sup-', [status(thm)], ['15', '16'])).
% 0.38/0.59  thf('18', plain,
% 0.38/0.59      ((![X0 : $i]:
% 0.38/0.59          (((k2_tarski @ X0 @ sk_A) = (k1_xboole_0))
% 0.38/0.59           | ((sk_B @ (k2_tarski @ X0 @ sk_A)) != (sk_A))))
% 0.38/0.59         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.38/0.59      inference('sup-', [status(thm)], ['7', '17'])).
% 0.38/0.59  thf('19', plain,
% 0.38/0.59      (((((sk_A) != (sk_A))
% 0.38/0.59         | ((k2_tarski @ sk_A @ sk_A) = (k1_xboole_0))
% 0.38/0.59         | ((k2_tarski @ sk_A @ sk_A) = (k1_xboole_0))))
% 0.38/0.59         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.38/0.59      inference('sup-', [status(thm)], ['5', '18'])).
% 0.38/0.59  thf('20', plain,
% 0.38/0.59      ((((k2_tarski @ sk_A @ sk_A) = (k1_xboole_0)))
% 0.38/0.59         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.38/0.59      inference('simplify', [status(thm)], ['19'])).
% 0.38/0.59  thf('21', plain,
% 0.38/0.59      (![X6 : $i, X9 : $i]: (r2_hidden @ X6 @ (k2_tarski @ X9 @ X6))),
% 0.38/0.59      inference('simplify', [status(thm)], ['6'])).
% 0.38/0.59  thf('22', plain,
% 0.38/0.59      (((r2_hidden @ sk_A @ k1_xboole_0)) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.38/0.59      inference('sup+', [status(thm)], ['20', '21'])).
% 0.38/0.59  thf('23', plain,
% 0.38/0.59      (![X1 : $i]:
% 0.38/0.59         (((k2_tarski @ X1 @ X1) = (k1_xboole_0))
% 0.38/0.59          | ((sk_B @ (k2_tarski @ X1 @ X1)) = (X1)))),
% 0.38/0.59      inference('simplify', [status(thm)], ['4'])).
% 0.38/0.59  thf('24', plain,
% 0.38/0.59      (![X6 : $i, X9 : $i]: (r2_hidden @ X6 @ (k2_tarski @ X9 @ X6))),
% 0.38/0.59      inference('simplify', [status(thm)], ['6'])).
% 0.38/0.59  thf('25', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('26', plain,
% 0.38/0.59      (![X17 : $i, X19 : $i]: ((k2_mcart_1 @ (k4_tarski @ X17 @ X19)) = (X19))),
% 0.38/0.59      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.38/0.59  thf('27', plain, (((k2_mcart_1 @ sk_A) = (sk_C))),
% 0.38/0.59      inference('sup+', [status(thm)], ['25', '26'])).
% 0.38/0.59  thf('28', plain,
% 0.38/0.59      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.38/0.59      inference('split', [status(esa)], ['11'])).
% 0.38/0.59  thf('29', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.38/0.59      inference('sup+', [status(thm)], ['27', '28'])).
% 0.38/0.59  thf('30', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('31', plain,
% 0.38/0.59      ((((sk_A) = (k4_tarski @ sk_B_1 @ sk_A)))
% 0.38/0.59         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.38/0.59      inference('sup+', [status(thm)], ['29', '30'])).
% 0.38/0.59  thf('32', plain,
% 0.38/0.59      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.38/0.59         (((X20) = (k1_xboole_0))
% 0.38/0.59          | ~ (r2_hidden @ X21 @ X20)
% 0.38/0.59          | ((sk_B @ X20) != (k4_tarski @ X22 @ X21)))),
% 0.38/0.59      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.38/0.59  thf('33', plain,
% 0.38/0.59      ((![X0 : $i]:
% 0.38/0.59          (((sk_B @ X0) != (sk_A))
% 0.38/0.59           | ~ (r2_hidden @ sk_A @ X0)
% 0.38/0.59           | ((X0) = (k1_xboole_0))))
% 0.38/0.59         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.38/0.59      inference('sup-', [status(thm)], ['31', '32'])).
% 0.38/0.59  thf('34', plain,
% 0.38/0.59      ((![X0 : $i]:
% 0.38/0.59          (((k2_tarski @ X0 @ sk_A) = (k1_xboole_0))
% 0.38/0.59           | ((sk_B @ (k2_tarski @ X0 @ sk_A)) != (sk_A))))
% 0.38/0.59         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.38/0.59      inference('sup-', [status(thm)], ['24', '33'])).
% 0.38/0.59  thf('35', plain,
% 0.38/0.59      (((((sk_A) != (sk_A))
% 0.38/0.59         | ((k2_tarski @ sk_A @ sk_A) = (k1_xboole_0))
% 0.38/0.59         | ((k2_tarski @ sk_A @ sk_A) = (k1_xboole_0))))
% 0.38/0.59         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.38/0.59      inference('sup-', [status(thm)], ['23', '34'])).
% 0.38/0.59  thf('36', plain,
% 0.38/0.59      ((((k2_tarski @ sk_A @ sk_A) = (k1_xboole_0)))
% 0.38/0.59         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.38/0.59      inference('simplify', [status(thm)], ['35'])).
% 0.38/0.59  thf('37', plain,
% 0.38/0.59      (![X6 : $i, X9 : $i]: (r2_hidden @ X6 @ (k2_tarski @ X9 @ X6))),
% 0.38/0.59      inference('simplify', [status(thm)], ['6'])).
% 0.38/0.59  thf('38', plain,
% 0.38/0.59      (((r2_hidden @ sk_A @ k1_xboole_0)) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.38/0.59      inference('sup+', [status(thm)], ['36', '37'])).
% 0.38/0.59  thf('39', plain,
% 0.38/0.59      (![X20 : $i]:
% 0.38/0.59         (((X20) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X20) @ X20))),
% 0.38/0.59      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.38/0.59  thf(d5_xboole_0, axiom,
% 0.38/0.59    (![A:$i,B:$i,C:$i]:
% 0.38/0.59     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.38/0.59       ( ![D:$i]:
% 0.38/0.59         ( ( r2_hidden @ D @ C ) <=>
% 0.38/0.59           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.38/0.59  thf('40', plain,
% 0.38/0.59      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.38/0.59         (~ (r2_hidden @ X4 @ X3)
% 0.38/0.59          | (r2_hidden @ X4 @ X1)
% 0.38/0.59          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.38/0.59      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.38/0.59  thf('41', plain,
% 0.38/0.59      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.38/0.59         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.38/0.59      inference('simplify', [status(thm)], ['40'])).
% 0.38/0.59  thf('42', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.38/0.59          | (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.38/0.59      inference('sup-', [status(thm)], ['39', '41'])).
% 0.38/0.59  thf('43', plain,
% 0.38/0.59      (![X20 : $i]:
% 0.38/0.59         (((X20) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X20) @ X20))),
% 0.38/0.59      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.38/0.59  thf('44', plain,
% 0.38/0.59      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.38/0.59         (~ (r2_hidden @ X4 @ X3)
% 0.38/0.59          | ~ (r2_hidden @ X4 @ X2)
% 0.38/0.59          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.38/0.59      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.38/0.59  thf('45', plain,
% 0.38/0.59      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.38/0.59         (~ (r2_hidden @ X4 @ X2)
% 0.38/0.59          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.38/0.59      inference('simplify', [status(thm)], ['44'])).
% 0.38/0.59  thf('46', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.38/0.59          | ~ (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['43', '45'])).
% 0.38/0.59  thf('47', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))
% 0.38/0.59          | ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['42', '46'])).
% 0.38/0.59  thf('48', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.38/0.59      inference('simplify', [status(thm)], ['47'])).
% 0.38/0.59  thf('49', plain,
% 0.38/0.59      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.38/0.59         (~ (r2_hidden @ X4 @ X2)
% 0.38/0.59          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.38/0.59      inference('simplify', [status(thm)], ['44'])).
% 0.38/0.59  thf('50', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['48', '49'])).
% 0.38/0.59  thf('51', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.38/0.59      inference('condensation', [status(thm)], ['50'])).
% 0.38/0.59  thf('52', plain, (~ (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['38', '51'])).
% 0.38/0.59  thf('53', plain,
% 0.38/0.59      ((((sk_A) = (k1_mcart_1 @ sk_A))) | (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.38/0.59      inference('split', [status(esa)], ['11'])).
% 0.38/0.59  thf('54', plain, ((((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.38/0.59      inference('sat_resolution*', [status(thm)], ['52', '53'])).
% 0.38/0.59  thf('55', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.38/0.59      inference('simpl_trail', [status(thm)], ['22', '54'])).
% 0.38/0.59  thf('56', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.38/0.59      inference('condensation', [status(thm)], ['50'])).
% 0.38/0.59  thf('57', plain, ($false), inference('sup-', [status(thm)], ['55', '56'])).
% 0.38/0.59  
% 0.38/0.59  % SZS output end Refutation
% 0.38/0.59  
% 0.38/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
