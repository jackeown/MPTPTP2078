%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BRbcmvnvRI

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:19 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 105 expanded)
%              Number of leaves         :    9 (  28 expanded)
%              Depth                    :   14
%              Number of atoms          :  513 (1087 expanded)
%              Number of equality atoms :   54 ( 120 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t67_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
      <=> ~ ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t67_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( X7 != X6 )
      | ( r2_hidden @ X7 @ X8 )
      | ( X8
       != ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('6',plain,(
    ! [X6: $i] :
      ( r2_hidden @ X6 @ ( k1_tarski @ X6 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('9',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('12',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','12'])).

thf('14',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','13'])).

thf('15',plain,(
    ! [X6: $i,X10: $i] :
      ( ( X10
        = ( k1_tarski @ X6 ) )
      | ( ( sk_C @ X10 @ X6 )
        = X6 )
      | ( r2_hidden @ ( sk_C @ X10 @ X6 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('16',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('17',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
        = X2 )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X8 )
      | ( X9 = X6 )
      | ( X8
       != ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('20',plain,(
    ! [X6: $i,X9: $i] :
      ( ( X9 = X6 )
      | ~ ( r2_hidden @ X9 @ ( k1_tarski @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X2 )
        = ( k1_tarski @ X1 ) )
      | ( ( sk_C @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) @ X1 )
        = X1 )
      | ( ( sk_C @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 != X2 )
      | ( ( sk_C @ ( k4_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) @ X0 )
        = X2 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X2 ) @ X1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['21'])).

thf('23',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X2 ) @ X1 )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C @ ( k4_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) @ X2 )
        = X2 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X6: $i] :
      ( r2_hidden @ X6 @ ( k1_tarski @ X6 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X2 ) @ X1 )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C @ ( k4_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) @ X2 )
        = X2 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('29',plain,(
    ! [X6: $i,X10: $i] :
      ( ( X10
        = ( k1_tarski @ X6 ) )
      | ( ( sk_C @ X10 @ X6 )
       != X6 )
      | ~ ( r2_hidden @ ( sk_C @ X10 @ X6 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) @ X0 )
       != X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) @ X0 )
       != X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( ( sk_C @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) @ X1 )
       != X1 ) ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('36',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('37',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','12','36'])).

thf('38',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['35','37'])).

thf('39',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['34','38'])).

thf('40',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['14','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BRbcmvnvRI
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:33:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.58  % Solved by: fo/fo7.sh
% 0.22/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.58  % done 159 iterations in 0.116s
% 0.22/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.58  % SZS output start Refutation
% 0.22/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.58  thf(t67_zfmisc_1, conjecture,
% 0.22/0.58    (![A:$i,B:$i]:
% 0.22/0.58     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.22/0.58       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.22/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.58    (~( ![A:$i,B:$i]:
% 0.22/0.58        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.22/0.58          ( ~( r2_hidden @ A @ B ) ) ) )),
% 0.22/0.58    inference('cnf.neg', [status(esa)], [t67_zfmisc_1])).
% 0.22/0.58  thf('0', plain,
% 0.22/0.58      ((~ (r2_hidden @ sk_A @ sk_B)
% 0.22/0.58        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('1', plain,
% 0.22/0.58      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.22/0.58      inference('split', [status(esa)], ['0'])).
% 0.22/0.58  thf('2', plain,
% 0.22/0.58      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.22/0.58       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.22/0.58      inference('split', [status(esa)], ['0'])).
% 0.22/0.58  thf('3', plain,
% 0.22/0.58      (((r2_hidden @ sk_A @ sk_B)
% 0.22/0.58        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A)))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('4', plain,
% 0.22/0.58      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.22/0.58      inference('split', [status(esa)], ['3'])).
% 0.22/0.58  thf(d1_tarski, axiom,
% 0.22/0.58    (![A:$i,B:$i]:
% 0.22/0.58     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.22/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.22/0.58  thf('5', plain,
% 0.22/0.58      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.58         (((X7) != (X6)) | (r2_hidden @ X7 @ X8) | ((X8) != (k1_tarski @ X6)))),
% 0.22/0.58      inference('cnf', [status(esa)], [d1_tarski])).
% 0.22/0.58  thf('6', plain, (![X6 : $i]: (r2_hidden @ X6 @ (k1_tarski @ X6))),
% 0.22/0.58      inference('simplify', [status(thm)], ['5'])).
% 0.22/0.58  thf('7', plain,
% 0.22/0.58      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))
% 0.22/0.58         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.22/0.58      inference('split', [status(esa)], ['0'])).
% 0.22/0.58  thf(d5_xboole_0, axiom,
% 0.22/0.58    (![A:$i,B:$i,C:$i]:
% 0.22/0.58     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.22/0.58       ( ![D:$i]:
% 0.22/0.58         ( ( r2_hidden @ D @ C ) <=>
% 0.22/0.58           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.22/0.58  thf('8', plain,
% 0.22/0.58      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.58         (~ (r2_hidden @ X4 @ X3)
% 0.22/0.58          | ~ (r2_hidden @ X4 @ X2)
% 0.22/0.58          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.22/0.58      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.22/0.58  thf('9', plain,
% 0.22/0.58      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.22/0.58         (~ (r2_hidden @ X4 @ X2)
% 0.22/0.58          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.22/0.58      inference('simplify', [status(thm)], ['8'])).
% 0.22/0.58  thf('10', plain,
% 0.22/0.58      ((![X0 : $i]:
% 0.22/0.58          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B)))
% 0.22/0.58         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.22/0.58      inference('sup-', [status(thm)], ['7', '9'])).
% 0.22/0.58  thf('11', plain,
% 0.22/0.58      ((~ (r2_hidden @ sk_A @ sk_B))
% 0.22/0.58         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.22/0.58      inference('sup-', [status(thm)], ['6', '10'])).
% 0.22/0.58  thf('12', plain,
% 0.22/0.58      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) | 
% 0.22/0.58       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.22/0.58      inference('sup-', [status(thm)], ['4', '11'])).
% 0.22/0.58  thf('13', plain, (~ ((r2_hidden @ sk_A @ sk_B))),
% 0.22/0.58      inference('sat_resolution*', [status(thm)], ['2', '12'])).
% 0.22/0.58  thf('14', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.22/0.58      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.22/0.58  thf('15', plain,
% 0.22/0.58      (![X6 : $i, X10 : $i]:
% 0.22/0.58         (((X10) = (k1_tarski @ X6))
% 0.22/0.58          | ((sk_C @ X10 @ X6) = (X6))
% 0.22/0.58          | (r2_hidden @ (sk_C @ X10 @ X6) @ X10))),
% 0.22/0.58      inference('cnf', [status(esa)], [d1_tarski])).
% 0.22/0.58  thf('16', plain,
% 0.22/0.58      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.58         (~ (r2_hidden @ X4 @ X3)
% 0.22/0.58          | (r2_hidden @ X4 @ X1)
% 0.22/0.58          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.22/0.58      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.22/0.58  thf('17', plain,
% 0.22/0.58      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.22/0.58         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.22/0.58      inference('simplify', [status(thm)], ['16'])).
% 0.22/0.58  thf('18', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.58         (((sk_C @ (k4_xboole_0 @ X1 @ X0) @ X2) = (X2))
% 0.22/0.58          | ((k4_xboole_0 @ X1 @ X0) = (k1_tarski @ X2))
% 0.22/0.58          | (r2_hidden @ (sk_C @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X1))),
% 0.22/0.58      inference('sup-', [status(thm)], ['15', '17'])).
% 0.22/0.58  thf('19', plain,
% 0.22/0.58      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.22/0.58         (~ (r2_hidden @ X9 @ X8) | ((X9) = (X6)) | ((X8) != (k1_tarski @ X6)))),
% 0.22/0.58      inference('cnf', [status(esa)], [d1_tarski])).
% 0.22/0.58  thf('20', plain,
% 0.22/0.58      (![X6 : $i, X9 : $i]:
% 0.22/0.58         (((X9) = (X6)) | ~ (r2_hidden @ X9 @ (k1_tarski @ X6)))),
% 0.22/0.58      inference('simplify', [status(thm)], ['19'])).
% 0.22/0.58  thf('21', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.58         (((k4_xboole_0 @ (k1_tarski @ X0) @ X2) = (k1_tarski @ X1))
% 0.22/0.58          | ((sk_C @ (k4_xboole_0 @ (k1_tarski @ X0) @ X2) @ X1) = (X1))
% 0.22/0.58          | ((sk_C @ (k4_xboole_0 @ (k1_tarski @ X0) @ X2) @ X1) = (X0)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['18', '20'])).
% 0.22/0.58  thf('22', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.58         (((X0) != (X2))
% 0.22/0.58          | ((sk_C @ (k4_xboole_0 @ (k1_tarski @ X2) @ X1) @ X0) = (X2))
% 0.22/0.58          | ((k4_xboole_0 @ (k1_tarski @ X2) @ X1) = (k1_tarski @ X0)))),
% 0.22/0.58      inference('eq_fact', [status(thm)], ['21'])).
% 0.22/0.58  thf('23', plain,
% 0.22/0.58      (![X1 : $i, X2 : $i]:
% 0.22/0.58         (((k4_xboole_0 @ (k1_tarski @ X2) @ X1) = (k1_tarski @ X2))
% 0.22/0.58          | ((sk_C @ (k4_xboole_0 @ (k1_tarski @ X2) @ X1) @ X2) = (X2)))),
% 0.22/0.58      inference('simplify', [status(thm)], ['22'])).
% 0.22/0.58  thf('24', plain, (![X6 : $i]: (r2_hidden @ X6 @ (k1_tarski @ X6))),
% 0.22/0.58      inference('simplify', [status(thm)], ['5'])).
% 0.22/0.58  thf('25', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.58         (~ (r2_hidden @ X0 @ X1)
% 0.22/0.58          | (r2_hidden @ X0 @ X2)
% 0.22/0.58          | (r2_hidden @ X0 @ X3)
% 0.22/0.58          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.22/0.58      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.22/0.58  thf('26', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.58         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.22/0.58          | (r2_hidden @ X0 @ X2)
% 0.22/0.58          | ~ (r2_hidden @ X0 @ X1))),
% 0.22/0.58      inference('simplify', [status(thm)], ['25'])).
% 0.22/0.58  thf('27', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         ((r2_hidden @ X0 @ X1)
% 0.22/0.58          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['24', '26'])).
% 0.22/0.58  thf('28', plain,
% 0.22/0.58      (![X1 : $i, X2 : $i]:
% 0.22/0.58         (((k4_xboole_0 @ (k1_tarski @ X2) @ X1) = (k1_tarski @ X2))
% 0.22/0.58          | ((sk_C @ (k4_xboole_0 @ (k1_tarski @ X2) @ X1) @ X2) = (X2)))),
% 0.22/0.58      inference('simplify', [status(thm)], ['22'])).
% 0.22/0.58  thf('29', plain,
% 0.22/0.58      (![X6 : $i, X10 : $i]:
% 0.22/0.58         (((X10) = (k1_tarski @ X6))
% 0.22/0.58          | ((sk_C @ X10 @ X6) != (X6))
% 0.22/0.58          | ~ (r2_hidden @ (sk_C @ X10 @ X6) @ X10))),
% 0.22/0.58      inference('cnf', [status(esa)], [d1_tarski])).
% 0.22/0.58  thf('30', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         (~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.22/0.58          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 0.22/0.58          | ((sk_C @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1) @ X0) != (X0))
% 0.22/0.58          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.58  thf('31', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         (((sk_C @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1) @ X0) != (X0))
% 0.22/0.58          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 0.22/0.58          | ~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.22/0.58      inference('simplify', [status(thm)], ['30'])).
% 0.22/0.58  thf('32', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         ((r2_hidden @ X1 @ X0)
% 0.22/0.58          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1))
% 0.22/0.58          | ((sk_C @ (k4_xboole_0 @ (k1_tarski @ X1) @ X0) @ X1) != (X1)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['27', '31'])).
% 0.22/0.58  thf('33', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         (((X0) != (X0))
% 0.22/0.58          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 0.22/0.58          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 0.22/0.58          | (r2_hidden @ X0 @ X1))),
% 0.22/0.58      inference('sup-', [status(thm)], ['23', '32'])).
% 0.22/0.58  thf('34', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         ((r2_hidden @ X0 @ X1)
% 0.22/0.58          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0)))),
% 0.22/0.58      inference('simplify', [status(thm)], ['33'])).
% 0.22/0.58  thf('35', plain,
% 0.22/0.58      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A)))
% 0.22/0.58         <= (~
% 0.22/0.58             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.22/0.58      inference('split', [status(esa)], ['3'])).
% 0.22/0.58  thf('36', plain,
% 0.22/0.58      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) | 
% 0.22/0.58       ((r2_hidden @ sk_A @ sk_B))),
% 0.22/0.58      inference('split', [status(esa)], ['3'])).
% 0.22/0.58  thf('37', plain,
% 0.22/0.58      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.22/0.58      inference('sat_resolution*', [status(thm)], ['2', '12', '36'])).
% 0.22/0.58  thf('38', plain,
% 0.22/0.58      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 0.22/0.58      inference('simpl_trail', [status(thm)], ['35', '37'])).
% 0.22/0.58  thf('39', plain,
% 0.22/0.58      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A)) | (r2_hidden @ sk_A @ sk_B))),
% 0.22/0.58      inference('sup-', [status(thm)], ['34', '38'])).
% 0.22/0.58  thf('40', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.22/0.58      inference('simplify', [status(thm)], ['39'])).
% 0.22/0.58  thf('41', plain, ($false), inference('demod', [status(thm)], ['14', '40'])).
% 0.22/0.58  
% 0.22/0.58  % SZS output end Refutation
% 0.22/0.58  
% 0.22/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
