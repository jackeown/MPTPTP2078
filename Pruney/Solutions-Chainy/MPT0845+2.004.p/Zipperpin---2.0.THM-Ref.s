%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bewYk9MXEI

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   55 (  65 expanded)
%              Number of leaves         :   19 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :  326 ( 464 expanded)
%              Number of equality atoms :   23 (  27 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('4',plain,(
    ! [X20: $i] :
      ( ( k1_ordinal1 @ X20 )
      = ( k2_xboole_0 @ X20 @ ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(t41_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X16 @ X15 ) @ X15 )
      | ( X15
        = ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf(t1_mcart_1,conjecture,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ( r1_xboole_0 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ! [B: $i] :
              ~ ( ( r2_hidden @ B @ A )
                & ( r1_xboole_0 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t1_mcart_1])).

thf('6',plain,(
    ! [X22: $i] :
      ( ~ ( r2_hidden @ X22 @ sk_A )
      | ~ ( r1_xboole_0 @ X22 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_tarski @ X0 ) )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( sk_C_1 @ X0 @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_tarski @ X0 ) )
      | ~ ( r1_xboole_0 @ ( sk_C_1 @ X0 @ sk_A ) @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

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

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t7_tarski,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ D @ B )
                    & ( r2_hidden @ D @ C ) ) ) ) )).

thf('11',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ( r2_hidden @ ( sk_C_2 @ X18 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C_2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X22: $i] :
      ( ~ ( r2_hidden @ X22 @ sk_A )
      | ~ ( r1_xboole_0 @ X22 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r1_xboole_0 @ ( sk_C_2 @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('17',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( r2_hidden @ X19 @ X18 )
      | ~ ( r2_hidden @ X19 @ ( sk_C_2 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( sk_C_2 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( sk_C_2 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( sk_C_2 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( sk_C_2 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ ( sk_C_2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( sk_C_2 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ X0 ) ),
    inference(demod,[status(thm)],['14','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['9','29'])).

thf('31',plain,(
    ! [X20: $i] :
      ( ( k1_ordinal1 @ X20 )
      = ( k2_xboole_0 @ X20 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','30'])).

thf('32',plain,
    ( ( k1_ordinal1 @ sk_A )
    = sk_A ),
    inference('sup+',[status(thm)],['3','31'])).

thf(t14_ordinal1,axiom,(
    ! [A: $i] :
      ( A
     != ( k1_ordinal1 @ A ) ) )).

thf('33',plain,(
    ! [X21: $i] :
      ( X21
     != ( k1_ordinal1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t14_ordinal1])).

thf('34',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['32','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bewYk9MXEI
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:16:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 63 iterations in 0.025s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.21/0.47  thf(sk_C_2_type, type, sk_C_2: $i > $i).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.21/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.47  thf(d10_xboole_0, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.21/0.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.47  thf('1', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.21/0.47      inference('simplify', [status(thm)], ['0'])).
% 0.21/0.47  thf(t12_xboole_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X7 : $i, X8 : $i]:
% 0.21/0.47         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.21/0.47      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.47  thf('3', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf(d1_ordinal1, axiom,
% 0.21/0.47    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X20 : $i]:
% 0.21/0.47         ((k1_ordinal1 @ X20) = (k2_xboole_0 @ X20 @ (k1_tarski @ X20)))),
% 0.21/0.47      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.21/0.47  thf(t41_zfmisc_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.47          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X15 : $i, X16 : $i]:
% 0.21/0.47         (((X15) = (k1_xboole_0))
% 0.21/0.47          | (r2_hidden @ (sk_C_1 @ X16 @ X15) @ X15)
% 0.21/0.47          | ((X15) = (k1_tarski @ X16)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 0.21/0.47  thf(t1_mcart_1, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.47          ( ![B:$i]: ( ~( ( r2_hidden @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.47             ( ![B:$i]:
% 0.21/0.47               ( ~( ( r2_hidden @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t1_mcart_1])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X22 : $i]: (~ (r2_hidden @ X22 @ sk_A) | ~ (r1_xboole_0 @ X22 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (((sk_A) = (k1_tarski @ X0))
% 0.21/0.47          | ((sk_A) = (k1_xboole_0))
% 0.21/0.47          | ~ (r1_xboole_0 @ (sk_C_1 @ X0 @ sk_A) @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.47  thf('8', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (((sk_A) = (k1_tarski @ X0))
% 0.21/0.47          | ~ (r1_xboole_0 @ (sk_C_1 @ X0 @ sk_A) @ sk_A))),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.21/0.47  thf(t3_xboole_0, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.21/0.47            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.47       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.47            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.47  thf(t7_tarski, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ~( ( r2_hidden @ A @ B ) & 
% 0.21/0.47          ( ![C:$i]:
% 0.21/0.47            ( ~( ( r2_hidden @ C @ B ) & 
% 0.21/0.47                 ( ![D:$i]:
% 0.21/0.47                   ( ~( ( r2_hidden @ D @ B ) & ( r2_hidden @ D @ C ) ) ) ) ) ) ) ) ))).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X17 : $i, X18 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X17 @ X18) | (r2_hidden @ (sk_C_2 @ X18) @ X18))),
% 0.21/0.47      inference('cnf', [status(esa)], [t7_tarski])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C_2 @ X0) @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (![X22 : $i]: (~ (r2_hidden @ X22 @ sk_A) | ~ (r1_xboole_0 @ X22 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r1_xboole_0 @ sk_A @ X0) | ~ (r1_xboole_0 @ (sk_C_2 @ sk_A) @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.21/0.47      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X17 @ X18)
% 0.21/0.47          | ~ (r2_hidden @ X19 @ X18)
% 0.21/0.47          | ~ (r2_hidden @ X19 @ (sk_C_2 @ X18)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t7_tarski])).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X1 @ (sk_C_2 @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 0.21/0.47      inference('condensation', [status(thm)], ['17'])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((r1_xboole_0 @ (sk_C_2 @ X0) @ X1)
% 0.21/0.47          | ~ (r2_hidden @ (sk_C @ X1 @ (sk_C_2 @ X0)) @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['16', '18'])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r1_xboole_0 @ (sk_C_2 @ X0) @ X0)
% 0.21/0.47          | (r1_xboole_0 @ (sk_C_2 @ X0) @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['15', '19'])).
% 0.21/0.47  thf('21', plain, (![X0 : $i]: (r1_xboole_0 @ (sk_C_2 @ X0) @ X0)),
% 0.21/0.47      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.47  thf('22', plain, (![X0 : $i]: (r1_xboole_0 @ sk_A @ X0)),
% 0.21/0.47      inference('demod', [status(thm)], ['14', '21'])).
% 0.21/0.47  thf('23', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.21/0.48      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X2 @ X0)
% 0.21/0.48          | ~ (r2_hidden @ X2 @ X3)
% 0.21/0.48          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.21/0.48      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ X1 @ X0)
% 0.21/0.48          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.21/0.48          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.21/0.48      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ X0 @ X1)
% 0.21/0.48          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.21/0.48          | (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['23', '26'])).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.48      inference('simplify', [status(thm)], ['27'])).
% 0.21/0.48  thf('29', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ sk_A)),
% 0.21/0.48      inference('sup-', [status(thm)], ['22', '28'])).
% 0.21/0.48  thf('30', plain, (![X0 : $i]: ((sk_A) = (k1_tarski @ X0))),
% 0.21/0.48      inference('demod', [status(thm)], ['9', '29'])).
% 0.21/0.48  thf('31', plain,
% 0.21/0.48      (![X20 : $i]: ((k1_ordinal1 @ X20) = (k2_xboole_0 @ X20 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['4', '30'])).
% 0.21/0.48  thf('32', plain, (((k1_ordinal1 @ sk_A) = (sk_A))),
% 0.21/0.48      inference('sup+', [status(thm)], ['3', '31'])).
% 0.21/0.48  thf(t14_ordinal1, axiom, (![A:$i]: ( ( A ) != ( k1_ordinal1 @ A ) ))).
% 0.21/0.48  thf('33', plain, (![X21 : $i]: ((X21) != (k1_ordinal1 @ X21))),
% 0.21/0.48      inference('cnf', [status(esa)], [t14_ordinal1])).
% 0.21/0.48  thf('34', plain, ($false),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['32', '33'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
