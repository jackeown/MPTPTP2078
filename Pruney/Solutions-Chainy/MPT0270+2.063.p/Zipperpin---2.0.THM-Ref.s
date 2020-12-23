%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.F1o1sXF6ur

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:20 EST 2020

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :   52 (  98 expanded)
%              Number of leaves         :   11 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :  458 ( 941 expanded)
%              Number of equality atoms :   48 (  96 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('5',plain,(
    ! [X14: $i] :
      ( ( k2_tarski @ X14 @ X14 )
      = ( k1_tarski @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X9 != X8 )
      | ( r2_hidden @ X9 @ X10 )
      | ( X10
       != ( k2_tarski @ X11 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('7',plain,(
    ! [X8: $i,X11: $i] :
      ( r2_hidden @ X8 @ ( k2_tarski @ X11 @ X8 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','7'])).

thf('9',plain,
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

thf('10',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('11',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf('14',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','13'])).

thf('15',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','14'])).

thf('16',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','15'])).

thf('17',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['17'])).

thf('19',plain,(
    ! [X14: $i] :
      ( ( k2_tarski @ X14 @ X14 )
      = ( k1_tarski @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('20',plain,(
    ! [X8: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ( X12 = X11 )
      | ( X12 = X8 )
      | ( X10
       != ( k2_tarski @ X11 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('21',plain,(
    ! [X8: $i,X11: $i,X12: $i] :
      ( ( X12 = X8 )
      | ( X12 = X11 )
      | ~ ( r2_hidden @ X12 @ ( k2_tarski @ X11 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['17'])).

thf('26',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['17'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['24','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('34',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('35',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','14','34'])).

thf('36',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['33','35'])).

thf('37',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['32','36'])).

thf('38',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['16','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.F1o1sXF6ur
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:15:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.74/1.00  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.74/1.00  % Solved by: fo/fo7.sh
% 0.74/1.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.74/1.00  % done 551 iterations in 0.541s
% 0.74/1.00  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.74/1.00  % SZS output start Refutation
% 0.74/1.00  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.74/1.00  thf(sk_A_type, type, sk_A: $i).
% 0.74/1.00  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.74/1.00  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.74/1.00  thf(sk_B_type, type, sk_B: $i).
% 0.74/1.00  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.74/1.00  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.74/1.00  thf(t67_zfmisc_1, conjecture,
% 0.74/1.00    (![A:$i,B:$i]:
% 0.74/1.00     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.74/1.00       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.74/1.00  thf(zf_stmt_0, negated_conjecture,
% 0.74/1.00    (~( ![A:$i,B:$i]:
% 0.74/1.00        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.74/1.00          ( ~( r2_hidden @ A @ B ) ) ) )),
% 0.74/1.00    inference('cnf.neg', [status(esa)], [t67_zfmisc_1])).
% 0.74/1.00  thf('0', plain,
% 0.74/1.00      ((~ (r2_hidden @ sk_A @ sk_B)
% 0.74/1.00        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.74/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.00  thf('1', plain,
% 0.74/1.00      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.74/1.00      inference('split', [status(esa)], ['0'])).
% 0.74/1.00  thf('2', plain,
% 0.74/1.00      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.74/1.00       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.74/1.00      inference('split', [status(esa)], ['0'])).
% 0.74/1.00  thf('3', plain,
% 0.74/1.00      (((r2_hidden @ sk_A @ sk_B)
% 0.74/1.00        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A)))),
% 0.74/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.00  thf('4', plain,
% 0.74/1.00      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.74/1.00      inference('split', [status(esa)], ['3'])).
% 0.74/1.00  thf(t69_enumset1, axiom,
% 0.74/1.00    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.74/1.00  thf('5', plain, (![X14 : $i]: ((k2_tarski @ X14 @ X14) = (k1_tarski @ X14))),
% 0.74/1.00      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.74/1.00  thf(d2_tarski, axiom,
% 0.74/1.00    (![A:$i,B:$i,C:$i]:
% 0.74/1.00     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.74/1.00       ( ![D:$i]:
% 0.74/1.00         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.74/1.00  thf('6', plain,
% 0.74/1.00      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.74/1.00         (((X9) != (X8))
% 0.74/1.00          | (r2_hidden @ X9 @ X10)
% 0.74/1.00          | ((X10) != (k2_tarski @ X11 @ X8)))),
% 0.74/1.00      inference('cnf', [status(esa)], [d2_tarski])).
% 0.74/1.00  thf('7', plain,
% 0.74/1.00      (![X8 : $i, X11 : $i]: (r2_hidden @ X8 @ (k2_tarski @ X11 @ X8))),
% 0.74/1.00      inference('simplify', [status(thm)], ['6'])).
% 0.74/1.00  thf('8', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.74/1.00      inference('sup+', [status(thm)], ['5', '7'])).
% 0.74/1.00  thf('9', plain,
% 0.74/1.00      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))
% 0.74/1.00         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.74/1.00      inference('split', [status(esa)], ['0'])).
% 0.74/1.00  thf(d5_xboole_0, axiom,
% 0.74/1.00    (![A:$i,B:$i,C:$i]:
% 0.74/1.00     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.74/1.00       ( ![D:$i]:
% 0.74/1.00         ( ( r2_hidden @ D @ C ) <=>
% 0.74/1.00           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.74/1.00  thf('10', plain,
% 0.74/1.00      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.74/1.00         (~ (r2_hidden @ X4 @ X3)
% 0.74/1.00          | ~ (r2_hidden @ X4 @ X2)
% 0.74/1.00          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.74/1.00      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.74/1.00  thf('11', plain,
% 0.74/1.00      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.74/1.00         (~ (r2_hidden @ X4 @ X2)
% 0.74/1.00          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.74/1.00      inference('simplify', [status(thm)], ['10'])).
% 0.74/1.00  thf('12', plain,
% 0.74/1.00      ((![X0 : $i]:
% 0.74/1.00          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B)))
% 0.74/1.00         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.74/1.00      inference('sup-', [status(thm)], ['9', '11'])).
% 0.74/1.00  thf('13', plain,
% 0.74/1.00      ((~ (r2_hidden @ sk_A @ sk_B))
% 0.74/1.00         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.74/1.00      inference('sup-', [status(thm)], ['8', '12'])).
% 0.74/1.00  thf('14', plain,
% 0.74/1.00      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) | 
% 0.74/1.00       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.74/1.00      inference('sup-', [status(thm)], ['4', '13'])).
% 0.74/1.00  thf('15', plain, (~ ((r2_hidden @ sk_A @ sk_B))),
% 0.74/1.00      inference('sat_resolution*', [status(thm)], ['2', '14'])).
% 0.74/1.00  thf('16', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.74/1.00      inference('simpl_trail', [status(thm)], ['1', '15'])).
% 0.74/1.00  thf('17', plain,
% 0.74/1.00      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.74/1.00         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.74/1.00          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.74/1.00          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.74/1.00      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.74/1.00  thf('18', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i]:
% 0.74/1.00         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.74/1.00          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.74/1.00      inference('eq_fact', [status(thm)], ['17'])).
% 0.74/1.00  thf('19', plain,
% 0.74/1.00      (![X14 : $i]: ((k2_tarski @ X14 @ X14) = (k1_tarski @ X14))),
% 0.74/1.00      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.74/1.00  thf('20', plain,
% 0.74/1.00      (![X8 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.74/1.00         (~ (r2_hidden @ X12 @ X10)
% 0.74/1.00          | ((X12) = (X11))
% 0.74/1.00          | ((X12) = (X8))
% 0.74/1.00          | ((X10) != (k2_tarski @ X11 @ X8)))),
% 0.74/1.00      inference('cnf', [status(esa)], [d2_tarski])).
% 0.74/1.00  thf('21', plain,
% 0.74/1.00      (![X8 : $i, X11 : $i, X12 : $i]:
% 0.74/1.00         (((X12) = (X8))
% 0.74/1.00          | ((X12) = (X11))
% 0.74/1.00          | ~ (r2_hidden @ X12 @ (k2_tarski @ X11 @ X8)))),
% 0.74/1.00      inference('simplify', [status(thm)], ['20'])).
% 0.74/1.00  thf('22', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i]:
% 0.74/1.00         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.74/1.00      inference('sup-', [status(thm)], ['19', '21'])).
% 0.74/1.00  thf('23', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i]:
% 0.74/1.00         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.74/1.00      inference('simplify', [status(thm)], ['22'])).
% 0.74/1.00  thf('24', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i]:
% 0.74/1.00         (((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.74/1.00          | ((sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.74/1.00      inference('sup-', [status(thm)], ['18', '23'])).
% 0.74/1.00  thf('25', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i]:
% 0.74/1.00         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.74/1.00          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.74/1.00      inference('eq_fact', [status(thm)], ['17'])).
% 0.74/1.00  thf('26', plain,
% 0.74/1.00      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.74/1.00         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.74/1.00          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.74/1.00          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.74/1.00          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.74/1.00      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.74/1.00  thf('27', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i]:
% 0.74/1.00         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 0.74/1.00          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.74/1.00          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.74/1.00          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.74/1.00      inference('sup-', [status(thm)], ['25', '26'])).
% 0.74/1.00  thf('28', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i]:
% 0.74/1.00         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.74/1.00          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.74/1.00          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.74/1.00      inference('simplify', [status(thm)], ['27'])).
% 0.74/1.00  thf('29', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i]:
% 0.74/1.00         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.74/1.00          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.74/1.00      inference('eq_fact', [status(thm)], ['17'])).
% 0.74/1.00  thf('30', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i]:
% 0.74/1.00         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 0.74/1.00          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 0.74/1.00      inference('clc', [status(thm)], ['28', '29'])).
% 0.74/1.00  thf('31', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i]:
% 0.74/1.00         ((r2_hidden @ X0 @ X1)
% 0.74/1.00          | ((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.74/1.00          | ((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.74/1.00      inference('sup+', [status(thm)], ['24', '30'])).
% 0.74/1.00  thf('32', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i]:
% 0.74/1.00         (((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.74/1.00          | (r2_hidden @ X0 @ X1))),
% 0.74/1.00      inference('simplify', [status(thm)], ['31'])).
% 0.74/1.00  thf('33', plain,
% 0.74/1.00      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A)))
% 0.74/1.00         <= (~
% 0.74/1.00             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.74/1.00      inference('split', [status(esa)], ['3'])).
% 0.74/1.00  thf('34', plain,
% 0.74/1.00      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) | 
% 0.74/1.00       ((r2_hidden @ sk_A @ sk_B))),
% 0.74/1.00      inference('split', [status(esa)], ['3'])).
% 0.74/1.00  thf('35', plain,
% 0.74/1.00      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.74/1.00      inference('sat_resolution*', [status(thm)], ['2', '14', '34'])).
% 0.74/1.00  thf('36', plain,
% 0.74/1.00      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 0.74/1.00      inference('simpl_trail', [status(thm)], ['33', '35'])).
% 0.74/1.00  thf('37', plain,
% 0.74/1.00      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A)) | (r2_hidden @ sk_A @ sk_B))),
% 0.74/1.00      inference('sup-', [status(thm)], ['32', '36'])).
% 0.74/1.00  thf('38', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.74/1.00      inference('simplify', [status(thm)], ['37'])).
% 0.74/1.00  thf('39', plain, ($false), inference('demod', [status(thm)], ['16', '38'])).
% 0.74/1.00  
% 0.74/1.00  % SZS output end Refutation
% 0.74/1.00  
% 0.74/1.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
