%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dFz7rEgMJy

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:48 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 109 expanded)
%              Number of leaves         :   11 (  31 expanded)
%              Depth                    :   15
%              Number of atoms          :  420 (1071 expanded)
%              Number of equality atoms :   56 ( 158 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('1',plain,(
    ! [X21: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X24 @ X23 )
      | ( X24 = X21 )
      | ( X23
       != ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('2',plain,(
    ! [X21: $i,X24: $i] :
      ( ( X24 = X21 )
      | ~ ( r2_hidden @ X24 @ ( k1_tarski @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t20_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
      <=> ( A != B ) ) ),
    inference('cnf.neg',[status(esa)],[t20_zfmisc_1])).

thf('9',plain,
    ( ( sk_A = sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,
    ( ( sk_A != sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( sk_A != sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['9'])).

thf('14',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['11'])).

thf('15',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['9'])).

thf('17',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_xboole_0 @ X6 @ X8 )
      | ( ( k4_xboole_0 @ X6 @ X8 )
       != X6 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('19',plain,
    ( ( ( ( k1_tarski @ sk_B )
       != ( k1_tarski @ sk_B ) )
      | ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( X22 != X21 )
      | ( r2_hidden @ X22 @ X23 )
      | ( X23
       != ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('22',plain,(
    ! [X21: $i] :
      ( r2_hidden @ X21 @ ( k1_tarski @ X21 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup-',[status(thm)],['20','24'])).

thf('26',plain,(
    ! [X21: $i] :
      ( r2_hidden @ X21 @ ( k1_tarski @ X21 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('27',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) )
    | ( sk_A != sk_B ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) )
    | ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['9'])).

thf('29',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['12','27','28'])).

thf('30',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['10','29'])).

thf('31',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','30'])).

thf('32',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X21: $i,X24: $i] :
      ( ( X24 = X21 )
      | ~ ( r2_hidden @ X24 @ ( k1_tarski @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('34',plain,(
    sk_A = sk_B ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_A != sk_B )
   <= ( sk_A != sk_B ) ),
    inference(split,[status(esa)],['11'])).

thf('36',plain,(
    sk_A != sk_B ),
    inference('sat_resolution*',[status(thm)],['12','27'])).

thf('37',plain,(
    sk_A != sk_B ),
    inference(simpl_trail,[status(thm)],['35','36'])).

thf('38',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['34','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dFz7rEgMJy
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:21:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 57 iterations in 0.031s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.49  thf(t3_xboole_0, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.22/0.49            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.49       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.22/0.49            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.22/0.49      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.49  thf(d1_tarski, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.22/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      (![X21 : $i, X23 : $i, X24 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X24 @ X23)
% 0.22/0.49          | ((X24) = (X21))
% 0.22/0.49          | ((X23) != (k1_tarski @ X21)))),
% 0.22/0.49      inference('cnf', [status(esa)], [d1_tarski])).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      (![X21 : $i, X24 : $i]:
% 0.22/0.49         (((X24) = (X21)) | ~ (r2_hidden @ X24 @ (k1_tarski @ X21)))),
% 0.22/0.49      inference('simplify', [status(thm)], ['1'])).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.22/0.49          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['0', '2'])).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((r2_hidden @ X0 @ X1)
% 0.22/0.49          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.22/0.49          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.22/0.49      inference('sup+', [status(thm)], ['3', '4'])).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.22/0.49      inference('simplify', [status(thm)], ['5'])).
% 0.22/0.49  thf(t83_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      (![X6 : $i, X7 : $i]:
% 0.22/0.49         (((k4_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 0.22/0.49      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((r2_hidden @ X1 @ X0)
% 0.22/0.49          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.49  thf(t20_zfmisc_1, conjecture,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.22/0.49         ( k1_tarski @ A ) ) <=>
% 0.22/0.49       ( ( A ) != ( B ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i,B:$i]:
% 0.22/0.49        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.22/0.49            ( k1_tarski @ A ) ) <=>
% 0.22/0.49          ( ( A ) != ( B ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t20_zfmisc_1])).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      ((((sk_A) = (sk_B))
% 0.22/0.49        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.22/0.49            != (k1_tarski @ sk_A)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.22/0.49          != (k1_tarski @ sk_A)))
% 0.22/0.49         <= (~
% 0.22/0.49             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.22/0.49                = (k1_tarski @ sk_A))))),
% 0.22/0.49      inference('split', [status(esa)], ['9'])).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      ((((sk_A) != (sk_B))
% 0.22/0.49        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.22/0.49            = (k1_tarski @ sk_A)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (~ (((sk_A) = (sk_B))) | 
% 0.22/0.49       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.22/0.49          = (k1_tarski @ sk_A)))),
% 0.22/0.49      inference('split', [status(esa)], ['11'])).
% 0.22/0.49  thf('13', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 0.22/0.49      inference('split', [status(esa)], ['9'])).
% 0.22/0.49  thf('14', plain,
% 0.22/0.49      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.22/0.49          = (k1_tarski @ sk_A)))
% 0.22/0.49         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.22/0.49                = (k1_tarski @ sk_A))))),
% 0.22/0.49      inference('split', [status(esa)], ['11'])).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B))
% 0.22/0.49          = (k1_tarski @ sk_A)))
% 0.22/0.49         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.22/0.49                = (k1_tarski @ sk_A))) & 
% 0.22/0.49             (((sk_A) = (sk_B))))),
% 0.22/0.49      inference('sup+', [status(thm)], ['13', '14'])).
% 0.22/0.49  thf('16', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 0.22/0.49      inference('split', [status(esa)], ['9'])).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B))
% 0.22/0.49          = (k1_tarski @ sk_B)))
% 0.22/0.49         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.22/0.49                = (k1_tarski @ sk_A))) & 
% 0.22/0.49             (((sk_A) = (sk_B))))),
% 0.22/0.49      inference('demod', [status(thm)], ['15', '16'])).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      (![X6 : $i, X8 : $i]:
% 0.22/0.49         ((r1_xboole_0 @ X6 @ X8) | ((k4_xboole_0 @ X6 @ X8) != (X6)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      (((((k1_tarski @ sk_B) != (k1_tarski @ sk_B))
% 0.22/0.49         | (r1_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B))))
% 0.22/0.49         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.22/0.49                = (k1_tarski @ sk_A))) & 
% 0.22/0.49             (((sk_A) = (sk_B))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      (((r1_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B)))
% 0.22/0.49         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.22/0.49                = (k1_tarski @ sk_A))) & 
% 0.22/0.49             (((sk_A) = (sk_B))))),
% 0.22/0.49      inference('simplify', [status(thm)], ['19'])).
% 0.22/0.49  thf('21', plain,
% 0.22/0.49      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.22/0.49         (((X22) != (X21))
% 0.22/0.49          | (r2_hidden @ X22 @ X23)
% 0.22/0.49          | ((X23) != (k1_tarski @ X21)))),
% 0.22/0.49      inference('cnf', [status(esa)], [d1_tarski])).
% 0.22/0.49  thf('22', plain, (![X21 : $i]: (r2_hidden @ X21 @ (k1_tarski @ X21))),
% 0.22/0.49      inference('simplify', [status(thm)], ['21'])).
% 0.22/0.49  thf('23', plain,
% 0.22/0.49      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X2 @ X0)
% 0.22/0.49          | ~ (r2_hidden @ X2 @ X3)
% 0.22/0.49          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.22/0.49      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.49  thf('24', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.22/0.49      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.49  thf('25', plain,
% 0.22/0.49      ((~ (r2_hidden @ sk_B @ (k1_tarski @ sk_B)))
% 0.22/0.49         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.22/0.49                = (k1_tarski @ sk_A))) & 
% 0.22/0.49             (((sk_A) = (sk_B))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['20', '24'])).
% 0.22/0.49  thf('26', plain, (![X21 : $i]: (r2_hidden @ X21 @ (k1_tarski @ X21))),
% 0.22/0.49      inference('simplify', [status(thm)], ['21'])).
% 0.22/0.49  thf('27', plain,
% 0.22/0.49      (~
% 0.22/0.49       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.22/0.49          = (k1_tarski @ sk_A))) | 
% 0.22/0.49       ~ (((sk_A) = (sk_B)))),
% 0.22/0.49      inference('demod', [status(thm)], ['25', '26'])).
% 0.22/0.49  thf('28', plain,
% 0.22/0.49      (~
% 0.22/0.49       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.22/0.49          = (k1_tarski @ sk_A))) | 
% 0.22/0.49       (((sk_A) = (sk_B)))),
% 0.22/0.49      inference('split', [status(esa)], ['9'])).
% 0.22/0.49  thf('29', plain,
% 0.22/0.49      (~
% 0.22/0.49       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.22/0.49          = (k1_tarski @ sk_A)))),
% 0.22/0.49      inference('sat_resolution*', [status(thm)], ['12', '27', '28'])).
% 0.22/0.49  thf('30', plain,
% 0.22/0.49      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.22/0.49         != (k1_tarski @ sk_A))),
% 0.22/0.49      inference('simpl_trail', [status(thm)], ['10', '29'])).
% 0.22/0.49  thf('31', plain,
% 0.22/0.49      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.22/0.49        | (r2_hidden @ sk_A @ (k1_tarski @ sk_B)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['8', '30'])).
% 0.22/0.49  thf('32', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.22/0.49      inference('simplify', [status(thm)], ['31'])).
% 0.22/0.49  thf('33', plain,
% 0.22/0.49      (![X21 : $i, X24 : $i]:
% 0.22/0.49         (((X24) = (X21)) | ~ (r2_hidden @ X24 @ (k1_tarski @ X21)))),
% 0.22/0.49      inference('simplify', [status(thm)], ['1'])).
% 0.22/0.49  thf('34', plain, (((sk_A) = (sk_B))),
% 0.22/0.49      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.49  thf('35', plain, ((((sk_A) != (sk_B))) <= (~ (((sk_A) = (sk_B))))),
% 0.22/0.49      inference('split', [status(esa)], ['11'])).
% 0.22/0.49  thf('36', plain, (~ (((sk_A) = (sk_B)))),
% 0.22/0.49      inference('sat_resolution*', [status(thm)], ['12', '27'])).
% 0.22/0.49  thf('37', plain, (((sk_A) != (sk_B))),
% 0.22/0.49      inference('simpl_trail', [status(thm)], ['35', '36'])).
% 0.22/0.49  thf('38', plain, ($false),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['34', '37'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
