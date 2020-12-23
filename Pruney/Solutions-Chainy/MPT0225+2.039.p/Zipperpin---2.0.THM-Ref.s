%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5wHcQj6JqN

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:49 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   42 (  86 expanded)
%              Number of leaves         :   11 (  24 expanded)
%              Depth                    :   14
%              Number of atoms          :  337 ( 826 expanded)
%              Number of equality atoms :   52 ( 136 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('0',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X16 ) @ X17 )
      | ( r2_hidden @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X3 )
        = X2 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

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

thf('3',plain,
    ( ( sk_A = sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( sk_A != sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( sk_A != sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('8',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('9',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('11',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k4_xboole_0 @ X2 @ X4 )
       != X2 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('13',plain,
    ( ( ( ( k1_tarski @ sk_B )
       != ( k1_tarski @ sk_B ) )
      | ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t16_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        & ( A = B ) ) )).

thf('15',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X18 ) @ ( k1_tarski @ X19 ) )
      | ( X18 != X19 ) ) ),
    inference(cnf,[status(esa)],[t16_zfmisc_1])).

thf('16',plain,(
    ! [X19: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X19 ) @ ( k1_tarski @ X19 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) )
    | ( sk_A != sk_B ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) )
    | ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('19',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['6','17','18'])).

thf('20',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['4','19'])).

thf('21',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','20'])).

thf('22',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(simplify,[status(thm)],['21'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('23',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( X8 = X5 )
      | ( X7
       != ( k1_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('24',plain,(
    ! [X5: $i,X8: $i] :
      ( ( X8 = X5 )
      | ~ ( r2_hidden @ X8 @ ( k1_tarski @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    sk_A = sk_B ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,
    ( ( sk_A != sk_B )
   <= ( sk_A != sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('27',plain,(
    sk_A != sk_B ),
    inference('sat_resolution*',[status(thm)],['6','17'])).

thf('28',plain,(
    sk_A != sk_B ),
    inference(simpl_trail,[status(thm)],['26','27'])).

thf('29',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['25','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5wHcQj6JqN
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:35:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 39 iterations in 0.017s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(l27_zfmisc_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.19/0.46  thf('0', plain,
% 0.19/0.46      (![X16 : $i, X17 : $i]:
% 0.19/0.46         ((r1_xboole_0 @ (k1_tarski @ X16) @ X17) | (r2_hidden @ X16 @ X17))),
% 0.19/0.46      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.19/0.46  thf(t83_xboole_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.46  thf('1', plain,
% 0.19/0.46      (![X2 : $i, X3 : $i]:
% 0.19/0.46         (((k4_xboole_0 @ X2 @ X3) = (X2)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.19/0.46      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.19/0.46  thf('2', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         ((r2_hidden @ X1 @ X0)
% 0.19/0.46          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.46  thf(t20_zfmisc_1, conjecture,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.19/0.46         ( k1_tarski @ A ) ) <=>
% 0.19/0.46       ( ( A ) != ( B ) ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i,B:$i]:
% 0.19/0.46        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.19/0.46            ( k1_tarski @ A ) ) <=>
% 0.19/0.46          ( ( A ) != ( B ) ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t20_zfmisc_1])).
% 0.19/0.46  thf('3', plain,
% 0.19/0.46      ((((sk_A) = (sk_B))
% 0.19/0.46        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.46            != (k1_tarski @ sk_A)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('4', plain,
% 0.19/0.46      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.46          != (k1_tarski @ sk_A)))
% 0.19/0.46         <= (~
% 0.19/0.46             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.46                = (k1_tarski @ sk_A))))),
% 0.19/0.46      inference('split', [status(esa)], ['3'])).
% 0.19/0.46  thf('5', plain,
% 0.19/0.46      ((((sk_A) != (sk_B))
% 0.19/0.46        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.46            = (k1_tarski @ sk_A)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('6', plain,
% 0.19/0.46      (~ (((sk_A) = (sk_B))) | 
% 0.19/0.46       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.46          = (k1_tarski @ sk_A)))),
% 0.19/0.46      inference('split', [status(esa)], ['5'])).
% 0.19/0.46  thf('7', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 0.19/0.46      inference('split', [status(esa)], ['3'])).
% 0.19/0.46  thf('8', plain,
% 0.19/0.46      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.46          = (k1_tarski @ sk_A)))
% 0.19/0.46         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.46                = (k1_tarski @ sk_A))))),
% 0.19/0.46      inference('split', [status(esa)], ['5'])).
% 0.19/0.46  thf('9', plain,
% 0.19/0.46      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B))
% 0.19/0.46          = (k1_tarski @ sk_A)))
% 0.19/0.46         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.46                = (k1_tarski @ sk_A))) & 
% 0.19/0.46             (((sk_A) = (sk_B))))),
% 0.19/0.46      inference('sup+', [status(thm)], ['7', '8'])).
% 0.19/0.46  thf('10', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 0.19/0.46      inference('split', [status(esa)], ['3'])).
% 0.19/0.46  thf('11', plain,
% 0.19/0.46      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B))
% 0.19/0.46          = (k1_tarski @ sk_B)))
% 0.19/0.46         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.46                = (k1_tarski @ sk_A))) & 
% 0.19/0.46             (((sk_A) = (sk_B))))),
% 0.19/0.46      inference('demod', [status(thm)], ['9', '10'])).
% 0.19/0.46  thf('12', plain,
% 0.19/0.46      (![X2 : $i, X4 : $i]:
% 0.19/0.46         ((r1_xboole_0 @ X2 @ X4) | ((k4_xboole_0 @ X2 @ X4) != (X2)))),
% 0.19/0.46      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.19/0.46  thf('13', plain,
% 0.19/0.46      (((((k1_tarski @ sk_B) != (k1_tarski @ sk_B))
% 0.19/0.46         | (r1_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B))))
% 0.19/0.46         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.46                = (k1_tarski @ sk_A))) & 
% 0.19/0.46             (((sk_A) = (sk_B))))),
% 0.19/0.46      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.46  thf('14', plain,
% 0.19/0.46      (((r1_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B)))
% 0.19/0.46         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.46                = (k1_tarski @ sk_A))) & 
% 0.19/0.46             (((sk_A) = (sk_B))))),
% 0.19/0.46      inference('simplify', [status(thm)], ['13'])).
% 0.19/0.46  thf(t16_zfmisc_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) & 
% 0.19/0.46          ( ( A ) = ( B ) ) ) ))).
% 0.19/0.46  thf('15', plain,
% 0.19/0.46      (![X18 : $i, X19 : $i]:
% 0.19/0.46         (~ (r1_xboole_0 @ (k1_tarski @ X18) @ (k1_tarski @ X19))
% 0.19/0.46          | ((X18) != (X19)))),
% 0.19/0.46      inference('cnf', [status(esa)], [t16_zfmisc_1])).
% 0.19/0.46  thf('16', plain,
% 0.19/0.46      (![X19 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X19) @ (k1_tarski @ X19))),
% 0.19/0.46      inference('simplify', [status(thm)], ['15'])).
% 0.19/0.46  thf('17', plain,
% 0.19/0.46      (~
% 0.19/0.46       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.46          = (k1_tarski @ sk_A))) | 
% 0.19/0.46       ~ (((sk_A) = (sk_B)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['14', '16'])).
% 0.19/0.46  thf('18', plain,
% 0.19/0.46      (~
% 0.19/0.46       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.46          = (k1_tarski @ sk_A))) | 
% 0.19/0.46       (((sk_A) = (sk_B)))),
% 0.19/0.46      inference('split', [status(esa)], ['3'])).
% 0.19/0.46  thf('19', plain,
% 0.19/0.46      (~
% 0.19/0.46       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.46          = (k1_tarski @ sk_A)))),
% 0.19/0.46      inference('sat_resolution*', [status(thm)], ['6', '17', '18'])).
% 0.19/0.46  thf('20', plain,
% 0.19/0.46      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.46         != (k1_tarski @ sk_A))),
% 0.19/0.46      inference('simpl_trail', [status(thm)], ['4', '19'])).
% 0.19/0.46  thf('21', plain,
% 0.19/0.46      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.19/0.46        | (r2_hidden @ sk_A @ (k1_tarski @ sk_B)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['2', '20'])).
% 0.19/0.46  thf('22', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.19/0.46      inference('simplify', [status(thm)], ['21'])).
% 0.19/0.46  thf(d1_tarski, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.19/0.46       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.19/0.46  thf('23', plain,
% 0.19/0.46      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.19/0.46         (~ (r2_hidden @ X8 @ X7) | ((X8) = (X5)) | ((X7) != (k1_tarski @ X5)))),
% 0.19/0.46      inference('cnf', [status(esa)], [d1_tarski])).
% 0.19/0.46  thf('24', plain,
% 0.19/0.46      (![X5 : $i, X8 : $i]:
% 0.19/0.46         (((X8) = (X5)) | ~ (r2_hidden @ X8 @ (k1_tarski @ X5)))),
% 0.19/0.46      inference('simplify', [status(thm)], ['23'])).
% 0.19/0.46  thf('25', plain, (((sk_A) = (sk_B))),
% 0.19/0.46      inference('sup-', [status(thm)], ['22', '24'])).
% 0.19/0.46  thf('26', plain, ((((sk_A) != (sk_B))) <= (~ (((sk_A) = (sk_B))))),
% 0.19/0.46      inference('split', [status(esa)], ['5'])).
% 0.19/0.46  thf('27', plain, (~ (((sk_A) = (sk_B)))),
% 0.19/0.46      inference('sat_resolution*', [status(thm)], ['6', '17'])).
% 0.19/0.46  thf('28', plain, (((sk_A) != (sk_B))),
% 0.19/0.46      inference('simpl_trail', [status(thm)], ['26', '27'])).
% 0.19/0.46  thf('29', plain, ($false),
% 0.19/0.46      inference('simplify_reflect-', [status(thm)], ['25', '28'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
