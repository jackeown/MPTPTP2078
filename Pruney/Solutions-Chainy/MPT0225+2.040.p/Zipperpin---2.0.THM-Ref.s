%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OHlld33wmJ

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:50 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   44 (  90 expanded)
%              Number of leaves         :   11 (  26 expanded)
%              Depth                    :   12
%              Number of atoms          :  357 ( 848 expanded)
%              Number of equality atoms :   46 ( 123 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('0',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X20 ) @ X21 )
      | ( r2_hidden @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
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
    ( ( ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( sk_A != sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( sk_A != sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('10',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['7'])).

thf('11',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_xboole_0 @ X6 @ X8 )
      | ( ( k4_xboole_0 @ X6 @ X8 )
       != X6 ) ) ),
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

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('14',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( X10 != X9 )
      | ( r2_hidden @ X10 @ X11 )
      | ( X11
       != ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('15',plain,(
    ! [X9: $i] :
      ( r2_hidden @ X9 @ ( k1_tarski @ X9 ) ) ),
    inference(simplify,[status(thm)],['14'])).

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

thf('16',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup-',[status(thm)],['9','18'])).

thf('20',plain,(
    ! [X9: $i] :
      ( r2_hidden @ X9 @ ( k1_tarski @ X9 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('21',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) )
    | ( sk_A != sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) )
    | ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('23',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['8','21','22'])).

thf('24',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['6','23'])).

thf('25',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( X12 = X9 )
      | ( X11
       != ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('26',plain,(
    ! [X9: $i,X12: $i] :
      ( ( X12 = X9 )
      | ~ ( r2_hidden @ X12 @ ( k1_tarski @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    sk_A = sk_B ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,
    ( ( sk_A != sk_B )
   <= ( sk_A != sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('29',plain,(
    sk_A != sk_B ),
    inference('sat_resolution*',[status(thm)],['8','21'])).

thf('30',plain,(
    sk_A != sk_B ),
    inference(simpl_trail,[status(thm)],['28','29'])).

thf('31',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['27','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OHlld33wmJ
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:51:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 68 iterations in 0.034s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.46  thf(l27_zfmisc_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.20/0.46  thf('0', plain,
% 0.20/0.46      (![X20 : $i, X21 : $i]:
% 0.20/0.46         ((r1_xboole_0 @ (k1_tarski @ X20) @ X21) | (r2_hidden @ X20 @ X21))),
% 0.20/0.46      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.20/0.46  thf(t83_xboole_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      (![X6 : $i, X7 : $i]:
% 0.20/0.46         (((k4_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 0.20/0.46      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((r2_hidden @ X1 @ X0)
% 0.20/0.46          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.46  thf(t20_zfmisc_1, conjecture,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.46         ( k1_tarski @ A ) ) <=>
% 0.20/0.46       ( ( A ) != ( B ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i,B:$i]:
% 0.20/0.46        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.46            ( k1_tarski @ A ) ) <=>
% 0.20/0.46          ( ( A ) != ( B ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      ((((sk_A) = (sk_B))
% 0.20/0.46        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.46            != (k1_tarski @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.46          != (k1_tarski @ sk_A)))
% 0.20/0.46         <= (~
% 0.20/0.46             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.46                = (k1_tarski @ sk_A))))),
% 0.20/0.46      inference('split', [status(esa)], ['3'])).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.20/0.46         | (r2_hidden @ sk_A @ (k1_tarski @ sk_B))))
% 0.20/0.46         <= (~
% 0.20/0.46             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.46                = (k1_tarski @ sk_A))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['2', '4'])).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      (((r2_hidden @ sk_A @ (k1_tarski @ sk_B)))
% 0.20/0.46         <= (~
% 0.20/0.46             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.46                = (k1_tarski @ sk_A))))),
% 0.20/0.46      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      ((((sk_A) != (sk_B))
% 0.20/0.46        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.46            = (k1_tarski @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      (~ (((sk_A) = (sk_B))) | 
% 0.20/0.46       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.46          = (k1_tarski @ sk_A)))),
% 0.20/0.46      inference('split', [status(esa)], ['7'])).
% 0.20/0.46  thf('9', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 0.20/0.46      inference('split', [status(esa)], ['3'])).
% 0.20/0.46  thf('10', plain,
% 0.20/0.46      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.46          = (k1_tarski @ sk_A)))
% 0.20/0.46         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.46                = (k1_tarski @ sk_A))))),
% 0.20/0.46      inference('split', [status(esa)], ['7'])).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      (![X6 : $i, X8 : $i]:
% 0.20/0.46         ((r1_xboole_0 @ X6 @ X8) | ((k4_xboole_0 @ X6 @ X8) != (X6)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.46  thf('12', plain,
% 0.20/0.46      (((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.20/0.46         | (r1_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))))
% 0.20/0.46         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.46                = (k1_tarski @ sk_A))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.46  thf('13', plain,
% 0.20/0.46      (((r1_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 0.20/0.46         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.46                = (k1_tarski @ sk_A))))),
% 0.20/0.46      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.46  thf(d1_tarski, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.46       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.46  thf('14', plain,
% 0.20/0.46      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.46         (((X10) != (X9))
% 0.20/0.46          | (r2_hidden @ X10 @ X11)
% 0.20/0.46          | ((X11) != (k1_tarski @ X9)))),
% 0.20/0.46      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.46  thf('15', plain, (![X9 : $i]: (r2_hidden @ X9 @ (k1_tarski @ X9))),
% 0.20/0.46      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.46  thf(t3_xboole_0, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.20/0.46            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.46       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.46            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.46  thf('16', plain,
% 0.20/0.46      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.20/0.46         (~ (r2_hidden @ X2 @ X0)
% 0.20/0.46          | ~ (r2_hidden @ X2 @ X3)
% 0.20/0.46          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.20/0.46      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.46  thf('17', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.46      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.46  thf('18', plain,
% 0.20/0.46      ((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_B)))
% 0.20/0.46         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.46                = (k1_tarski @ sk_A))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['13', '17'])).
% 0.20/0.46  thf('19', plain,
% 0.20/0.46      ((~ (r2_hidden @ sk_B @ (k1_tarski @ sk_B)))
% 0.20/0.46         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.46                = (k1_tarski @ sk_A))) & 
% 0.20/0.46             (((sk_A) = (sk_B))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['9', '18'])).
% 0.20/0.46  thf('20', plain, (![X9 : $i]: (r2_hidden @ X9 @ (k1_tarski @ X9))),
% 0.20/0.46      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.46  thf('21', plain,
% 0.20/0.46      (~
% 0.20/0.46       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.46          = (k1_tarski @ sk_A))) | 
% 0.20/0.46       ~ (((sk_A) = (sk_B)))),
% 0.20/0.46      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.46  thf('22', plain,
% 0.20/0.46      (~
% 0.20/0.46       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.46          = (k1_tarski @ sk_A))) | 
% 0.20/0.46       (((sk_A) = (sk_B)))),
% 0.20/0.46      inference('split', [status(esa)], ['3'])).
% 0.20/0.46  thf('23', plain,
% 0.20/0.46      (~
% 0.20/0.46       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.46          = (k1_tarski @ sk_A)))),
% 0.20/0.46      inference('sat_resolution*', [status(thm)], ['8', '21', '22'])).
% 0.20/0.46  thf('24', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.20/0.46      inference('simpl_trail', [status(thm)], ['6', '23'])).
% 0.20/0.46  thf('25', plain,
% 0.20/0.46      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.20/0.46         (~ (r2_hidden @ X12 @ X11)
% 0.20/0.46          | ((X12) = (X9))
% 0.20/0.46          | ((X11) != (k1_tarski @ X9)))),
% 0.20/0.46      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.46  thf('26', plain,
% 0.20/0.46      (![X9 : $i, X12 : $i]:
% 0.20/0.46         (((X12) = (X9)) | ~ (r2_hidden @ X12 @ (k1_tarski @ X9)))),
% 0.20/0.46      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.46  thf('27', plain, (((sk_A) = (sk_B))),
% 0.20/0.46      inference('sup-', [status(thm)], ['24', '26'])).
% 0.20/0.46  thf('28', plain, ((((sk_A) != (sk_B))) <= (~ (((sk_A) = (sk_B))))),
% 0.20/0.46      inference('split', [status(esa)], ['7'])).
% 0.20/0.46  thf('29', plain, (~ (((sk_A) = (sk_B)))),
% 0.20/0.46      inference('sat_resolution*', [status(thm)], ['8', '21'])).
% 0.20/0.46  thf('30', plain, (((sk_A) != (sk_B))),
% 0.20/0.46      inference('simpl_trail', [status(thm)], ['28', '29'])).
% 0.20/0.46  thf('31', plain, ($false),
% 0.20/0.46      inference('simplify_reflect-', [status(thm)], ['27', '30'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
