%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4Ug4PXP48X

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 (  80 expanded)
%              Number of leaves         :   16 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :  329 ( 753 expanded)
%              Number of equality atoms :   30 (  72 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( X7 != X6 )
      | ( r2_hidden @ X7 @ X8 )
      | ( X8
       != ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('1',plain,(
    ! [X6: $i] :
      ( r2_hidden @ X6 @ ( k1_tarski @ X6 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t16_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k2_tarski @ C @ D ) ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( ( ( k2_mcart_1 @ A )
            = C )
          | ( ( k2_mcart_1 @ A )
            = D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k2_tarski @ C @ D ) ) )
       => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
          & ( ( ( k2_mcart_1 @ A )
              = C )
            | ( ( k2_mcart_1 @ A )
              = D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t16_mcart_1])).

thf('2',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('3',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X19 ) @ X21 )
      | ~ ( r2_hidden @ X19 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('4',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t144_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X16 @ X17 )
      | ( r2_hidden @ X18 @ X17 )
      | ( X17
        = ( k4_xboole_0 @ X17 @ ( k2_tarski @ X16 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[t144_zfmisc_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('6',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('7',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X3 @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_C_1 @ X0 )
      | ( r2_hidden @ sk_D_1 @ X0 )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','9'])).

thf('11',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X8 )
      | ( X9 = X6 )
      | ( X8
       != ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('12',plain,(
    ! [X6: $i,X9: $i] :
      ( ( X9 = X6 )
      | ~ ( r2_hidden @ X9 @ ( k1_tarski @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( r2_hidden @ sk_C_1 @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
    | ( sk_D_1
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X19 ) @ X20 )
      | ~ ( r2_hidden @ X19 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('18',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B )
   <= ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 )
    | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['14'])).

thf('23',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_D_1 ),
    inference('sat_resolution*',[status(thm)],['21','22'])).

thf('24',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_D_1 ),
    inference(simpl_trail,[status(thm)],['15','23'])).

thf('25',plain,(
    r2_hidden @ sk_C_1 @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['13','24'])).

thf('26',plain,(
    ! [X6: $i,X9: $i] :
      ( ( X9 = X6 )
      | ~ ( r2_hidden @ X9 @ ( k1_tarski @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('27',plain,
    ( sk_C_1
    = ( k2_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C_1 )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_C_1 ) ),
    inference(split,[status(esa)],['19'])).

thf('29',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C_1 )
    | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['19'])).

thf('30',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['21','29'])).

thf('31',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_C_1 ),
    inference(simpl_trail,[status(thm)],['28','30'])).

thf('32',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['27','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4Ug4PXP48X
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:02:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 41 iterations in 0.036s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.49  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.49  thf(d1_tarski, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.49         (((X7) != (X6)) | (r2_hidden @ X7 @ X8) | ((X8) != (k1_tarski @ X6)))),
% 0.21/0.49      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.49  thf('1', plain, (![X6 : $i]: (r2_hidden @ X6 @ (k1_tarski @ X6))),
% 0.21/0.49      inference('simplify', [status(thm)], ['0'])).
% 0.21/0.49  thf(t16_mcart_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k2_tarski @ C @ D ) ) ) =>
% 0.21/0.49       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.21/0.49         ( ( ( k2_mcart_1 @ A ) = ( C ) ) | ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k2_tarski @ C @ D ) ) ) =>
% 0.21/0.49          ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.21/0.49            ( ( ( k2_mcart_1 @ A ) = ( C ) ) | ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t16_mcart_1])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ (k2_tarski @ sk_C_1 @ sk_D_1)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t10_mcart_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.21/0.49       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.21/0.49         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.49         ((r2_hidden @ (k2_mcart_1 @ X19) @ X21)
% 0.21/0.49          | ~ (r2_hidden @ X19 @ (k2_zfmisc_1 @ X20 @ X21)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      ((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.49  thf(t144_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 0.21/0.49          ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ))).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.49         ((r2_hidden @ X16 @ X17)
% 0.21/0.49          | (r2_hidden @ X18 @ X17)
% 0.21/0.49          | ((X17) = (k4_xboole_0 @ X17 @ (k2_tarski @ X16 @ X18))))),
% 0.21/0.49      inference('cnf', [status(esa)], [t144_zfmisc_1])).
% 0.21/0.49  thf(d5_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.21/0.49       ( ![D:$i]:
% 0.21/0.49         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.49           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X4 @ X3)
% 0.21/0.49          | ~ (r2_hidden @ X4 @ X2)
% 0.21/0.49          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.21/0.49      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X4 @ X2)
% 0.21/0.49          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X3 @ X0)
% 0.21/0.49          | (r2_hidden @ X1 @ X0)
% 0.21/0.49          | (r2_hidden @ X2 @ X0)
% 0.21/0.49          | ~ (r2_hidden @ X3 @ (k2_tarski @ X2 @ X1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['5', '7'])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r2_hidden @ sk_C_1 @ X0)
% 0.21/0.49          | (r2_hidden @ sk_D_1 @ X0)
% 0.21/0.49          | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['4', '8'])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (((r2_hidden @ sk_D_1 @ (k1_tarski @ (k2_mcart_1 @ sk_A)))
% 0.21/0.49        | (r2_hidden @ sk_C_1 @ (k1_tarski @ (k2_mcart_1 @ sk_A))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '9'])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X9 @ X8) | ((X9) = (X6)) | ((X8) != (k1_tarski @ X6)))),
% 0.21/0.49      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X6 : $i, X9 : $i]:
% 0.21/0.49         (((X9) = (X6)) | ~ (r2_hidden @ X9 @ (k1_tarski @ X6)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (((r2_hidden @ sk_C_1 @ (k1_tarski @ (k2_mcart_1 @ sk_A)))
% 0.21/0.49        | ((sk_D_1) = (k2_mcart_1 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['10', '12'])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      ((~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)
% 0.21/0.49        | ((k2_mcart_1 @ sk_A) != (sk_D_1)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      ((((k2_mcart_1 @ sk_A) != (sk_D_1)))
% 0.21/0.49         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D_1))))),
% 0.21/0.49      inference('split', [status(esa)], ['14'])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ (k2_tarski @ sk_C_1 @ sk_D_1)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.49         ((r2_hidden @ (k1_mcart_1 @ X19) @ X20)
% 0.21/0.49          | ~ (r2_hidden @ X19 @ (k2_zfmisc_1 @ X20 @ X21)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.49  thf('18', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)),
% 0.21/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      ((~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)
% 0.21/0.49        | ((k2_mcart_1 @ sk_A) != (sk_C_1)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      ((~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))
% 0.21/0.49         <= (~ ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)))),
% 0.21/0.49      inference('split', [status(esa)], ['19'])).
% 0.21/0.49  thf('21', plain, (((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['18', '20'])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (~ (((k2_mcart_1 @ sk_A) = (sk_D_1))) | 
% 0.21/0.49       ~ ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))),
% 0.21/0.49      inference('split', [status(esa)], ['14'])).
% 0.21/0.49  thf('23', plain, (~ (((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['21', '22'])).
% 0.21/0.49  thf('24', plain, (((k2_mcart_1 @ sk_A) != (sk_D_1))),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['15', '23'])).
% 0.21/0.49  thf('25', plain, ((r2_hidden @ sk_C_1 @ (k1_tarski @ (k2_mcart_1 @ sk_A)))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['13', '24'])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (![X6 : $i, X9 : $i]:
% 0.21/0.49         (((X9) = (X6)) | ~ (r2_hidden @ X9 @ (k1_tarski @ X6)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.49  thf('27', plain, (((sk_C_1) = (k2_mcart_1 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      ((((k2_mcart_1 @ sk_A) != (sk_C_1)))
% 0.21/0.49         <= (~ (((k2_mcart_1 @ sk_A) = (sk_C_1))))),
% 0.21/0.49      inference('split', [status(esa)], ['19'])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      (~ (((k2_mcart_1 @ sk_A) = (sk_C_1))) | 
% 0.21/0.49       ~ ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))),
% 0.21/0.49      inference('split', [status(esa)], ['19'])).
% 0.21/0.49  thf('30', plain, (~ (((k2_mcart_1 @ sk_A) = (sk_C_1)))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['21', '29'])).
% 0.21/0.49  thf('31', plain, (((k2_mcart_1 @ sk_A) != (sk_C_1))),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['28', '30'])).
% 0.21/0.49  thf('32', plain, ($false),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['27', '31'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
