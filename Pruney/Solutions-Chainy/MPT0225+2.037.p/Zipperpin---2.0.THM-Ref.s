%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WCddZyy7r8

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:49 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   48 (  97 expanded)
%              Number of leaves         :   14 (  29 expanded)
%              Depth                    :   13
%              Number of atoms          :  356 ( 868 expanded)
%              Number of equality atoms :   50 ( 134 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('0',plain,(
    ! [X45: $i,X46: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X45 ) @ X46 )
      | ( r2_hidden @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_xboole_0 @ X9 @ X10 ) ) ),
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

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('13',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( X13 != X12 )
      | ( r2_hidden @ X13 @ X14 )
      | ( X14
       != ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('15',plain,(
    ! [X12: $i] :
      ( r2_hidden @ X12 @ ( k1_tarski @ X12 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('17',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X1 @ X4 ) )
      | ~ ( r1_xboole_0 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) )
    | ( sk_A != sk_B ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('21',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) )
    | ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('22',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['6','20','21'])).

thf('23',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['4','22'])).

thf('24',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','23'])).

thf('25',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X14 )
      | ( X15 = X12 )
      | ( X14
       != ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('27',plain,(
    ! [X12: $i,X15: $i] :
      ( ( X15 = X12 )
      | ~ ( r2_hidden @ X15 @ ( k1_tarski @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    sk_A = sk_B ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,
    ( ( sk_A != sk_B )
   <= ( sk_A != sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('30',plain,(
    sk_A != sk_B ),
    inference('sat_resolution*',[status(thm)],['6','20'])).

thf('31',plain,(
    sk_A != sk_B ),
    inference(simpl_trail,[status(thm)],['29','30'])).

thf('32',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['28','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WCddZyy7r8
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:40:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 61 iterations in 0.045s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.51  thf(l27_zfmisc_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.22/0.51  thf('0', plain,
% 0.22/0.51      (![X45 : $i, X46 : $i]:
% 0.22/0.51         ((r1_xboole_0 @ (k1_tarski @ X45) @ X46) | (r2_hidden @ X45 @ X46))),
% 0.22/0.51      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.22/0.51  thf(t83_xboole_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.51  thf('1', plain,
% 0.22/0.51      (![X9 : $i, X10 : $i]:
% 0.22/0.51         (((k4_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_xboole_0 @ X9 @ X10))),
% 0.22/0.51      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.22/0.51  thf('2', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         ((r2_hidden @ X1 @ X0)
% 0.22/0.51          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.51  thf(t20_zfmisc_1, conjecture,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.22/0.51         ( k1_tarski @ A ) ) <=>
% 0.22/0.51       ( ( A ) != ( B ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i,B:$i]:
% 0.22/0.51        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.22/0.51            ( k1_tarski @ A ) ) <=>
% 0.22/0.51          ( ( A ) != ( B ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t20_zfmisc_1])).
% 0.22/0.51  thf('3', plain,
% 0.22/0.51      ((((sk_A) = (sk_B))
% 0.22/0.51        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.22/0.51            != (k1_tarski @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('4', plain,
% 0.22/0.51      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.22/0.51          != (k1_tarski @ sk_A)))
% 0.22/0.51         <= (~
% 0.22/0.51             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.22/0.51                = (k1_tarski @ sk_A))))),
% 0.22/0.51      inference('split', [status(esa)], ['3'])).
% 0.22/0.51  thf('5', plain,
% 0.22/0.51      ((((sk_A) != (sk_B))
% 0.22/0.51        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.22/0.51            = (k1_tarski @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('6', plain,
% 0.22/0.51      (~ (((sk_A) = (sk_B))) | 
% 0.22/0.51       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.22/0.51          = (k1_tarski @ sk_A)))),
% 0.22/0.51      inference('split', [status(esa)], ['5'])).
% 0.22/0.51  thf('7', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 0.22/0.51      inference('split', [status(esa)], ['3'])).
% 0.22/0.51  thf('8', plain,
% 0.22/0.51      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.22/0.51          = (k1_tarski @ sk_A)))
% 0.22/0.51         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.22/0.51                = (k1_tarski @ sk_A))))),
% 0.22/0.51      inference('split', [status(esa)], ['5'])).
% 0.22/0.51  thf('9', plain,
% 0.22/0.51      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B))
% 0.22/0.51          = (k1_tarski @ sk_A)))
% 0.22/0.51         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.22/0.51                = (k1_tarski @ sk_A))) & 
% 0.22/0.51             (((sk_A) = (sk_B))))),
% 0.22/0.51      inference('sup+', [status(thm)], ['7', '8'])).
% 0.22/0.51  thf('10', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 0.22/0.51      inference('split', [status(esa)], ['3'])).
% 0.22/0.51  thf('11', plain,
% 0.22/0.51      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B))
% 0.22/0.51          = (k1_tarski @ sk_B)))
% 0.22/0.51         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.22/0.51                = (k1_tarski @ sk_A))) & 
% 0.22/0.51             (((sk_A) = (sk_B))))),
% 0.22/0.51      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.51  thf(t79_xboole_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.22/0.51  thf('12', plain,
% 0.22/0.51      (![X7 : $i, X8 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ X8)),
% 0.22/0.51      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.22/0.51  thf('13', plain,
% 0.22/0.51      (((r1_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B)))
% 0.22/0.51         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.22/0.51                = (k1_tarski @ sk_A))) & 
% 0.22/0.51             (((sk_A) = (sk_B))))),
% 0.22/0.51      inference('sup+', [status(thm)], ['11', '12'])).
% 0.22/0.51  thf(d1_tarski, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.22/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.22/0.51  thf('14', plain,
% 0.22/0.51      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.51         (((X13) != (X12))
% 0.22/0.51          | (r2_hidden @ X13 @ X14)
% 0.22/0.51          | ((X14) != (k1_tarski @ X12)))),
% 0.22/0.51      inference('cnf', [status(esa)], [d1_tarski])).
% 0.22/0.51  thf('15', plain, (![X12 : $i]: (r2_hidden @ X12 @ (k1_tarski @ X12))),
% 0.22/0.51      inference('simplify', [status(thm)], ['14'])).
% 0.22/0.51  thf(idempotence_k3_xboole_0, axiom,
% 0.22/0.51    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.22/0.51  thf('16', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.22/0.51      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.22/0.51  thf(t4_xboole_0, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.51            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.51       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.22/0.51            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.22/0.51  thf('17', plain,
% 0.22/0.51      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X1 @ X4))
% 0.22/0.51          | ~ (r1_xboole_0 @ X1 @ X4))),
% 0.22/0.51      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.22/0.51  thf('18', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.51  thf('19', plain,
% 0.22/0.51      (![X0 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['15', '18'])).
% 0.22/0.51  thf('20', plain,
% 0.22/0.51      (~
% 0.22/0.51       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.22/0.51          = (k1_tarski @ sk_A))) | 
% 0.22/0.51       ~ (((sk_A) = (sk_B)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['13', '19'])).
% 0.22/0.51  thf('21', plain,
% 0.22/0.51      (~
% 0.22/0.51       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.22/0.51          = (k1_tarski @ sk_A))) | 
% 0.22/0.51       (((sk_A) = (sk_B)))),
% 0.22/0.51      inference('split', [status(esa)], ['3'])).
% 0.22/0.51  thf('22', plain,
% 0.22/0.51      (~
% 0.22/0.51       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.22/0.51          = (k1_tarski @ sk_A)))),
% 0.22/0.51      inference('sat_resolution*', [status(thm)], ['6', '20', '21'])).
% 0.22/0.51  thf('23', plain,
% 0.22/0.51      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.22/0.51         != (k1_tarski @ sk_A))),
% 0.22/0.51      inference('simpl_trail', [status(thm)], ['4', '22'])).
% 0.22/0.51  thf('24', plain,
% 0.22/0.51      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.22/0.51        | (r2_hidden @ sk_A @ (k1_tarski @ sk_B)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['2', '23'])).
% 0.22/0.51  thf('25', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.22/0.51      inference('simplify', [status(thm)], ['24'])).
% 0.22/0.51  thf('26', plain,
% 0.22/0.51      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X15 @ X14)
% 0.22/0.51          | ((X15) = (X12))
% 0.22/0.51          | ((X14) != (k1_tarski @ X12)))),
% 0.22/0.51      inference('cnf', [status(esa)], [d1_tarski])).
% 0.22/0.51  thf('27', plain,
% 0.22/0.51      (![X12 : $i, X15 : $i]:
% 0.22/0.51         (((X15) = (X12)) | ~ (r2_hidden @ X15 @ (k1_tarski @ X12)))),
% 0.22/0.51      inference('simplify', [status(thm)], ['26'])).
% 0.22/0.51  thf('28', plain, (((sk_A) = (sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['25', '27'])).
% 0.22/0.51  thf('29', plain, ((((sk_A) != (sk_B))) <= (~ (((sk_A) = (sk_B))))),
% 0.22/0.51      inference('split', [status(esa)], ['5'])).
% 0.22/0.51  thf('30', plain, (~ (((sk_A) = (sk_B)))),
% 0.22/0.51      inference('sat_resolution*', [status(thm)], ['6', '20'])).
% 0.22/0.51  thf('31', plain, (((sk_A) != (sk_B))),
% 0.22/0.51      inference('simpl_trail', [status(thm)], ['29', '30'])).
% 0.22/0.51  thf('32', plain, ($false),
% 0.22/0.51      inference('simplify_reflect-', [status(thm)], ['28', '31'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.36/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
