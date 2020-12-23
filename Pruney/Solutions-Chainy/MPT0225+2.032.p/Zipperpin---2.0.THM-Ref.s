%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uPChsqT9sP

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:49 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   42 (  82 expanded)
%              Number of leaves         :   11 (  24 expanded)
%              Depth                    :   14
%              Number of atoms          :  321 ( 748 expanded)
%              Number of equality atoms :   45 ( 114 expanded)
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
    ! [X21: $i,X22: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X21 ) @ X22 )
      | ( r2_hidden @ X21 @ X22 ) ) ),
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

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( X6 != X5 )
      | ( r2_hidden @ X6 @ X7 )
      | ( X7
       != ( k1_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('8',plain,(
    ! [X5: $i] :
      ( r2_hidden @ X5 @ ( k1_tarski @ X5 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('10',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('11',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k4_xboole_0 @ X2 @ X4 )
       != X2 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('12',plain,
    ( ( ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ sk_A ) )
      | ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('14',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X19 ) @ X20 )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('15',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf('17',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) )
    | ( sk_A != sk_B ) ),
    inference('sup-',[status(thm)],['8','16'])).

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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uPChsqT9sP
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:06:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 57 iterations in 0.029s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(l27_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (![X21 : $i, X22 : $i]:
% 0.20/0.48         ((r1_xboole_0 @ (k1_tarski @ X21) @ X22) | (r2_hidden @ X21 @ X22))),
% 0.20/0.48      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.20/0.48  thf(t83_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X2 : $i, X3 : $i]:
% 0.20/0.48         (((k4_xboole_0 @ X2 @ X3) = (X2)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((r2_hidden @ X1 @ X0)
% 0.20/0.48          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.48  thf(t20_zfmisc_1, conjecture,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.48         ( k1_tarski @ A ) ) <=>
% 0.20/0.48       ( ( A ) != ( B ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i]:
% 0.20/0.48        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.48            ( k1_tarski @ A ) ) <=>
% 0.20/0.48          ( ( A ) != ( B ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      ((((sk_A) = (sk_B))
% 0.20/0.48        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.48            != (k1_tarski @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.48          != (k1_tarski @ sk_A)))
% 0.20/0.48         <= (~
% 0.20/0.48             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.48                = (k1_tarski @ sk_A))))),
% 0.20/0.48      inference('split', [status(esa)], ['3'])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      ((((sk_A) != (sk_B))
% 0.20/0.48        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.48            = (k1_tarski @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (~ (((sk_A) = (sk_B))) | 
% 0.20/0.48       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.48          = (k1_tarski @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['5'])).
% 0.20/0.48  thf(d1_tarski, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.48         (((X6) != (X5)) | (r2_hidden @ X6 @ X7) | ((X7) != (k1_tarski @ X5)))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.48  thf('8', plain, (![X5 : $i]: (r2_hidden @ X5 @ (k1_tarski @ X5))),
% 0.20/0.48      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.48  thf('9', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 0.20/0.48      inference('split', [status(esa)], ['3'])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.48          = (k1_tarski @ sk_A)))
% 0.20/0.48         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.48                = (k1_tarski @ sk_A))))),
% 0.20/0.48      inference('split', [status(esa)], ['5'])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X2 : $i, X4 : $i]:
% 0.20/0.48         ((r1_xboole_0 @ X2 @ X4) | ((k4_xboole_0 @ X2 @ X4) != (X2)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.20/0.48         | (r1_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))))
% 0.20/0.48         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.48                = (k1_tarski @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (((r1_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 0.20/0.48         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.48                = (k1_tarski @ sk_A))))),
% 0.20/0.48      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.48  thf(l24_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X19 : $i, X20 : $i]:
% 0.20/0.48         (~ (r1_xboole_0 @ (k1_tarski @ X19) @ X20) | ~ (r2_hidden @ X19 @ X20))),
% 0.20/0.48      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      ((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_B)))
% 0.20/0.48         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.48                = (k1_tarski @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      ((~ (r2_hidden @ sk_B @ (k1_tarski @ sk_B)))
% 0.20/0.48         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.48                = (k1_tarski @ sk_A))) & 
% 0.20/0.48             (((sk_A) = (sk_B))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['9', '15'])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (~
% 0.20/0.48       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.48          = (k1_tarski @ sk_A))) | 
% 0.20/0.48       ~ (((sk_A) = (sk_B)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['8', '16'])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (~
% 0.20/0.48       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.48          = (k1_tarski @ sk_A))) | 
% 0.20/0.48       (((sk_A) = (sk_B)))),
% 0.20/0.48      inference('split', [status(esa)], ['3'])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (~
% 0.20/0.48       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.48          = (k1_tarski @ sk_A)))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['6', '17', '18'])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.48         != (k1_tarski @ sk_A))),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['4', '19'])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.20/0.48        | (r2_hidden @ sk_A @ (k1_tarski @ sk_B)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '20'])).
% 0.20/0.48  thf('22', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.20/0.48      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X8 @ X7) | ((X8) = (X5)) | ((X7) != (k1_tarski @ X5)))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (![X5 : $i, X8 : $i]:
% 0.20/0.48         (((X8) = (X5)) | ~ (r2_hidden @ X8 @ (k1_tarski @ X5)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.48  thf('25', plain, (((sk_A) = (sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['22', '24'])).
% 0.20/0.48  thf('26', plain, ((((sk_A) != (sk_B))) <= (~ (((sk_A) = (sk_B))))),
% 0.20/0.48      inference('split', [status(esa)], ['5'])).
% 0.20/0.48  thf('27', plain, (~ (((sk_A) = (sk_B)))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['6', '17'])).
% 0.20/0.48  thf('28', plain, (((sk_A) != (sk_B))),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['26', '27'])).
% 0.20/0.48  thf('29', plain, ($false),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['25', '28'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
