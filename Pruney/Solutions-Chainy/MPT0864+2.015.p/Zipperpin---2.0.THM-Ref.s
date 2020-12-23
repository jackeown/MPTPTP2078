%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8BvUoUNXw7

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:01 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 139 expanded)
%              Number of leaves         :   16 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :  507 (1242 expanded)
%              Number of equality atoms :   83 ( 205 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X19 != X18 )
      | ( r2_hidden @ X19 @ X20 )
      | ( X20
       != ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('1',plain,(
    ! [X18: $i] :
      ( r2_hidden @ X18 @ ( k1_tarski @ X18 ) ) ),
    inference(simplify,[status(thm)],['0'])).

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

thf('2',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('3',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X29 @ X30 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('4',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( sk_A = sk_B_1 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('8',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C_1 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

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

thf('10',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X32 = k1_xboole_0 )
      | ~ ( r2_hidden @ X34 @ X32 )
      | ( ( sk_B @ X32 )
       != ( k4_tarski @ X34 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('11',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_A )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ sk_A ) )
       != sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('13',plain,(
    ! [X32: $i] :
      ( ( X32 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X32 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('14',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ( X21 = X18 )
      | ( X20
       != ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('15',plain,(
    ! [X18: $i,X21: $i] :
      ( ( X21 = X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_tarski @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X18: $i] :
      ( r2_hidden @ X18 @ ( k1_tarski @ X18 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('19',plain,
    ( ( r2_hidden @ sk_A @ k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X32: $i] :
      ( ( X32 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X32 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('21',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('22',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X32: $i] :
      ( ( X32 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X32 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('25',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('26',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['31'])).

thf('33',plain,
    ( $false
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','32'])).

thf('34',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X29: $i,X31: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X29 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('36',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C_1 ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('38',plain,
    ( ( sk_A = sk_C_1 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('42',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X32 = k1_xboole_0 )
      | ~ ( r2_hidden @ X33 @ X32 )
      | ( ( sk_B @ X32 )
       != ( k4_tarski @ X34 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k4_tarski @ X2 @ X1 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) )
      | ( ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ ( k4_tarski @ sk_B_1 @ sk_A ) )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','44'])).

thf('46',plain,(
    ! [X18: $i] :
      ( r2_hidden @ X18 @ ( k1_tarski @ X18 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('47',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('48',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X18: $i] :
      ( r2_hidden @ X18 @ ( k1_tarski @ X18 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('50',plain,
    ( ( r2_hidden @ sk_A @ k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['31'])).

thf('52',plain,(
    sk_A
 != ( k2_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('54',plain,
    ( sk_A
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['52','53'])).

thf('55',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['33','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8BvUoUNXw7
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:17:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.52  % Solved by: fo/fo7.sh
% 0.19/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.52  % done 153 iterations in 0.076s
% 0.19/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.52  % SZS output start Refutation
% 0.19/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.52  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.19/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.52  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.19/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.52  thf(d1_tarski, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.19/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.19/0.52  thf('0', plain,
% 0.19/0.52      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.19/0.52         (((X19) != (X18))
% 0.19/0.52          | (r2_hidden @ X19 @ X20)
% 0.19/0.52          | ((X20) != (k1_tarski @ X18)))),
% 0.19/0.52      inference('cnf', [status(esa)], [d1_tarski])).
% 0.19/0.52  thf('1', plain, (![X18 : $i]: (r2_hidden @ X18 @ (k1_tarski @ X18))),
% 0.19/0.52      inference('simplify', [status(thm)], ['0'])).
% 0.19/0.52  thf(t20_mcart_1, conjecture,
% 0.19/0.52    (![A:$i]:
% 0.19/0.52     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.19/0.52       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.19/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.52    (~( ![A:$i]:
% 0.19/0.52        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.19/0.52          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.19/0.52    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.19/0.52  thf('2', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C_1))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(t7_mcart_1, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.19/0.52       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.19/0.52  thf('3', plain,
% 0.19/0.52      (![X29 : $i, X30 : $i]: ((k1_mcart_1 @ (k4_tarski @ X29 @ X30)) = (X29))),
% 0.19/0.52      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.19/0.52  thf('4', plain, (((k1_mcart_1 @ sk_A) = (sk_B_1))),
% 0.19/0.52      inference('sup+', [status(thm)], ['2', '3'])).
% 0.19/0.52  thf('5', plain,
% 0.19/0.52      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('6', plain,
% 0.19/0.52      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.19/0.52      inference('split', [status(esa)], ['5'])).
% 0.19/0.52  thf('7', plain,
% 0.19/0.52      ((((sk_A) = (sk_B_1))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.19/0.52      inference('sup+', [status(thm)], ['4', '6'])).
% 0.19/0.52  thf('8', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C_1))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('9', plain,
% 0.19/0.52      ((((sk_A) = (k4_tarski @ sk_A @ sk_C_1)))
% 0.19/0.52         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.19/0.52      inference('sup+', [status(thm)], ['7', '8'])).
% 0.19/0.52  thf(t9_mcart_1, axiom,
% 0.19/0.52    (![A:$i]:
% 0.19/0.52     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.19/0.52          ( ![B:$i]:
% 0.19/0.52            ( ~( ( r2_hidden @ B @ A ) & 
% 0.19/0.52                 ( ![C:$i,D:$i]:
% 0.19/0.52                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.19/0.52                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.52  thf('10', plain,
% 0.19/0.52      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.19/0.52         (((X32) = (k1_xboole_0))
% 0.19/0.52          | ~ (r2_hidden @ X34 @ X32)
% 0.19/0.52          | ((sk_B @ X32) != (k4_tarski @ X34 @ X33)))),
% 0.19/0.52      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.19/0.52  thf('11', plain,
% 0.19/0.52      ((![X0 : $i]:
% 0.19/0.52          (((sk_B @ X0) != (sk_A))
% 0.19/0.52           | ~ (r2_hidden @ sk_A @ X0)
% 0.19/0.52           | ((X0) = (k1_xboole_0))))
% 0.19/0.52         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.19/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.52  thf('12', plain,
% 0.19/0.52      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.19/0.52         | ((sk_B @ (k1_tarski @ sk_A)) != (sk_A))))
% 0.19/0.52         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.19/0.52      inference('sup-', [status(thm)], ['1', '11'])).
% 0.19/0.52  thf('13', plain,
% 0.19/0.52      (![X32 : $i]:
% 0.19/0.52         (((X32) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X32) @ X32))),
% 0.19/0.52      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.19/0.52  thf('14', plain,
% 0.19/0.52      (![X18 : $i, X20 : $i, X21 : $i]:
% 0.19/0.52         (~ (r2_hidden @ X21 @ X20)
% 0.19/0.52          | ((X21) = (X18))
% 0.19/0.52          | ((X20) != (k1_tarski @ X18)))),
% 0.19/0.52      inference('cnf', [status(esa)], [d1_tarski])).
% 0.19/0.52  thf('15', plain,
% 0.19/0.52      (![X18 : $i, X21 : $i]:
% 0.19/0.52         (((X21) = (X18)) | ~ (r2_hidden @ X21 @ (k1_tarski @ X18)))),
% 0.19/0.52      inference('simplify', [status(thm)], ['14'])).
% 0.19/0.52  thf('16', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.19/0.52          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['13', '15'])).
% 0.19/0.52  thf('17', plain,
% 0.19/0.52      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.19/0.52         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.19/0.52      inference('clc', [status(thm)], ['12', '16'])).
% 0.19/0.52  thf('18', plain, (![X18 : $i]: (r2_hidden @ X18 @ (k1_tarski @ X18))),
% 0.19/0.52      inference('simplify', [status(thm)], ['0'])).
% 0.19/0.52  thf('19', plain,
% 0.19/0.52      (((r2_hidden @ sk_A @ k1_xboole_0)) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.19/0.52      inference('sup+', [status(thm)], ['17', '18'])).
% 0.19/0.52  thf('20', plain,
% 0.19/0.52      (![X32 : $i]:
% 0.19/0.52         (((X32) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X32) @ X32))),
% 0.19/0.52      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.19/0.52  thf(d5_xboole_0, axiom,
% 0.19/0.52    (![A:$i,B:$i,C:$i]:
% 0.19/0.52     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.19/0.52       ( ![D:$i]:
% 0.19/0.52         ( ( r2_hidden @ D @ C ) <=>
% 0.19/0.52           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.19/0.52  thf('21', plain,
% 0.19/0.52      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.52         (~ (r2_hidden @ X4 @ X3)
% 0.19/0.52          | (r2_hidden @ X4 @ X1)
% 0.19/0.52          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.19/0.52      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.19/0.52  thf('22', plain,
% 0.19/0.52      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.19/0.52         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.19/0.52      inference('simplify', [status(thm)], ['21'])).
% 0.19/0.52  thf('23', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.19/0.52          | (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.19/0.52      inference('sup-', [status(thm)], ['20', '22'])).
% 0.19/0.52  thf('24', plain,
% 0.19/0.52      (![X32 : $i]:
% 0.19/0.52         (((X32) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X32) @ X32))),
% 0.19/0.52      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.19/0.52  thf('25', plain,
% 0.19/0.52      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.52         (~ (r2_hidden @ X4 @ X3)
% 0.19/0.52          | ~ (r2_hidden @ X4 @ X2)
% 0.19/0.52          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.19/0.52      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.19/0.52  thf('26', plain,
% 0.19/0.52      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.19/0.52         (~ (r2_hidden @ X4 @ X2)
% 0.19/0.52          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.19/0.52      inference('simplify', [status(thm)], ['25'])).
% 0.19/0.52  thf('27', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.19/0.52          | ~ (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.19/0.52      inference('sup-', [status(thm)], ['24', '26'])).
% 0.19/0.52  thf('28', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         (((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))
% 0.19/0.52          | ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['23', '27'])).
% 0.19/0.52  thf('29', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.19/0.52      inference('simplify', [status(thm)], ['28'])).
% 0.19/0.52  thf('30', plain,
% 0.19/0.52      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.19/0.52         (~ (r2_hidden @ X4 @ X2)
% 0.19/0.52          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.19/0.52      inference('simplify', [status(thm)], ['25'])).
% 0.19/0.52  thf('31', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.19/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.19/0.52  thf('32', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.19/0.52      inference('condensation', [status(thm)], ['31'])).
% 0.19/0.52  thf('33', plain, (($false) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.19/0.52      inference('sup-', [status(thm)], ['19', '32'])).
% 0.19/0.52  thf('34', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C_1))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('35', plain,
% 0.19/0.52      (![X29 : $i, X31 : $i]: ((k2_mcart_1 @ (k4_tarski @ X29 @ X31)) = (X31))),
% 0.19/0.52      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.19/0.52  thf('36', plain, (((k2_mcart_1 @ sk_A) = (sk_C_1))),
% 0.19/0.52      inference('sup+', [status(thm)], ['34', '35'])).
% 0.19/0.52  thf('37', plain,
% 0.19/0.52      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.19/0.52      inference('split', [status(esa)], ['5'])).
% 0.19/0.52  thf('38', plain,
% 0.19/0.52      ((((sk_A) = (sk_C_1))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.19/0.52      inference('sup+', [status(thm)], ['36', '37'])).
% 0.19/0.52  thf('39', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C_1))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('40', plain,
% 0.19/0.52      ((((sk_A) = (k4_tarski @ sk_B_1 @ sk_A)))
% 0.19/0.52         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.19/0.52      inference('sup+', [status(thm)], ['38', '39'])).
% 0.19/0.52  thf('41', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.19/0.52          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['13', '15'])).
% 0.19/0.52  thf('42', plain,
% 0.19/0.52      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.19/0.52         (((X32) = (k1_xboole_0))
% 0.19/0.52          | ~ (r2_hidden @ X33 @ X32)
% 0.19/0.52          | ((sk_B @ X32) != (k4_tarski @ X34 @ X33)))),
% 0.19/0.52      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.19/0.52  thf('43', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.52         (((X0) != (k4_tarski @ X2 @ X1))
% 0.19/0.52          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.19/0.52          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.19/0.52          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['41', '42'])).
% 0.19/0.52  thf('44', plain,
% 0.19/0.52      (![X1 : $i, X2 : $i]:
% 0.19/0.52         (~ (r2_hidden @ X1 @ (k1_tarski @ (k4_tarski @ X2 @ X1)))
% 0.19/0.52          | ((k1_tarski @ (k4_tarski @ X2 @ X1)) = (k1_xboole_0)))),
% 0.19/0.52      inference('simplify', [status(thm)], ['43'])).
% 0.19/0.52  thf('45', plain,
% 0.19/0.52      (((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A))
% 0.19/0.52         | ((k1_tarski @ (k4_tarski @ sk_B_1 @ sk_A)) = (k1_xboole_0))))
% 0.19/0.52         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.19/0.52      inference('sup-', [status(thm)], ['40', '44'])).
% 0.19/0.52  thf('46', plain, (![X18 : $i]: (r2_hidden @ X18 @ (k1_tarski @ X18))),
% 0.19/0.52      inference('simplify', [status(thm)], ['0'])).
% 0.19/0.52  thf('47', plain,
% 0.19/0.52      ((((sk_A) = (k4_tarski @ sk_B_1 @ sk_A)))
% 0.19/0.52         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.19/0.52      inference('sup+', [status(thm)], ['38', '39'])).
% 0.19/0.52  thf('48', plain,
% 0.19/0.52      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.19/0.52         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.19/0.52      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.19/0.52  thf('49', plain, (![X18 : $i]: (r2_hidden @ X18 @ (k1_tarski @ X18))),
% 0.19/0.52      inference('simplify', [status(thm)], ['0'])).
% 0.19/0.52  thf('50', plain,
% 0.19/0.52      (((r2_hidden @ sk_A @ k1_xboole_0)) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.19/0.52      inference('sup+', [status(thm)], ['48', '49'])).
% 0.19/0.52  thf('51', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.19/0.52      inference('condensation', [status(thm)], ['31'])).
% 0.19/0.52  thf('52', plain, (~ (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['50', '51'])).
% 0.19/0.52  thf('53', plain,
% 0.19/0.52      ((((sk_A) = (k1_mcart_1 @ sk_A))) | (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.19/0.52      inference('split', [status(esa)], ['5'])).
% 0.19/0.52  thf('54', plain, ((((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.19/0.52      inference('sat_resolution*', [status(thm)], ['52', '53'])).
% 0.19/0.52  thf('55', plain, ($false),
% 0.19/0.52      inference('simpl_trail', [status(thm)], ['33', '54'])).
% 0.19/0.52  
% 0.19/0.52  % SZS output end Refutation
% 0.19/0.52  
% 0.19/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
