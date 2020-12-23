%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PZjDV6fXA7

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:43 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 118 expanded)
%              Number of leaves         :   10 (  32 expanded)
%              Depth                    :   12
%              Number of atoms          :  378 ( 985 expanded)
%              Number of equality atoms :   32 (  90 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(t13_ordinal1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
      <=> ( ( r2_hidden @ A @ B )
          | ( A = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t13_ordinal1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( sk_A != sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
    | ( sk_A != sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( sk_A = sk_B )
    | ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('7',plain,(
    ! [X11: $i] :
      ( ( k1_ordinal1 @ X11 )
      = ( k2_xboole_0 @ X11 @ ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('9',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('12',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X8 )
      | ( X9 = X6 )
      | ( X8
       != ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('13',plain,(
    ! [X6: $i,X9: $i] :
      ( ( X9 = X6 )
      | ~ ( r2_hidden @ X9 @ ( k1_tarski @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ( sk_A = sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_A != sk_B )
   <= ( sk_A != sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('18',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != sk_B )
      & ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
    | ( r2_hidden @ sk_A @ sk_B )
    | ( sk_A = sk_B ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','19'])).

thf('21',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['1','20'])).

thf('22',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('23',plain,(
    ! [X11: $i] :
      ( ( k1_ordinal1 @ X11 )
      = ( k2_xboole_0 @ X11 @ ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('24',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['23','27'])).

thf('29',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('30',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( sk_A = sk_B )
    | ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('32',plain,(
    sk_A = sk_B ),
    inference('sat_resolution*',[status(thm)],['2','4','19','30','31'])).

thf('33',plain,(
    sk_A = sk_B ),
    inference(simpl_trail,[status(thm)],['22','32'])).

thf('34',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','33'])).

thf('35',plain,(
    ! [X11: $i] :
      ( ( k1_ordinal1 @ X11 )
      = ( k2_xboole_0 @ X11 @ ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('36',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( X7 != X6 )
      | ( r2_hidden @ X7 @ X8 )
      | ( X8
       != ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('37',plain,(
    ! [X6: $i] :
      ( r2_hidden @ X6 @ ( k1_tarski @ X6 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','40'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['34','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PZjDV6fXA7
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:34:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.55  % Solved by: fo/fo7.sh
% 0.37/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.55  % done 85 iterations in 0.050s
% 0.37/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.55  % SZS output start Refutation
% 0.37/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.55  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.37/0.55  thf(t13_ordinal1, conjecture,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.37/0.55       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.37/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.55    (~( ![A:$i,B:$i]:
% 0.37/0.55        ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.37/0.55          ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ) )),
% 0.37/0.55    inference('cnf.neg', [status(esa)], [t13_ordinal1])).
% 0.37/0.55  thf('0', plain,
% 0.37/0.55      ((~ (r2_hidden @ sk_A @ sk_B)
% 0.37/0.55        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('1', plain,
% 0.37/0.55      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.37/0.55         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.37/0.55      inference('split', [status(esa)], ['0'])).
% 0.37/0.55  thf('2', plain,
% 0.37/0.55      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.37/0.55       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.37/0.55      inference('split', [status(esa)], ['0'])).
% 0.37/0.55  thf('3', plain,
% 0.37/0.55      ((((sk_A) != (sk_B)) | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('4', plain,
% 0.37/0.55      (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) | ~ (((sk_A) = (sk_B)))),
% 0.37/0.55      inference('split', [status(esa)], ['3'])).
% 0.37/0.55  thf('5', plain,
% 0.37/0.55      ((((sk_A) = (sk_B))
% 0.37/0.55        | (r2_hidden @ sk_A @ sk_B)
% 0.37/0.55        | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('6', plain,
% 0.37/0.55      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.37/0.55         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.37/0.55      inference('split', [status(esa)], ['5'])).
% 0.37/0.55  thf(d1_ordinal1, axiom,
% 0.37/0.55    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.37/0.55  thf('7', plain,
% 0.37/0.55      (![X11 : $i]:
% 0.37/0.55         ((k1_ordinal1 @ X11) = (k2_xboole_0 @ X11 @ (k1_tarski @ X11)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.37/0.55  thf(d3_xboole_0, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.37/0.55       ( ![D:$i]:
% 0.37/0.55         ( ( r2_hidden @ D @ C ) <=>
% 0.37/0.55           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.37/0.55  thf('8', plain,
% 0.37/0.55      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X4 @ X2)
% 0.37/0.55          | (r2_hidden @ X4 @ X3)
% 0.37/0.55          | (r2_hidden @ X4 @ X1)
% 0.37/0.55          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.37/0.55  thf('9', plain,
% 0.37/0.55      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.37/0.55         ((r2_hidden @ X4 @ X1)
% 0.37/0.55          | (r2_hidden @ X4 @ X3)
% 0.37/0.55          | ~ (r2_hidden @ X4 @ (k2_xboole_0 @ X3 @ X1)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['8'])).
% 0.37/0.55  thf('10', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.37/0.55          | (r2_hidden @ X1 @ X0)
% 0.37/0.55          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['7', '9'])).
% 0.37/0.55  thf('11', plain,
% 0.37/0.55      ((((r2_hidden @ sk_A @ (k1_tarski @ sk_B)) | (r2_hidden @ sk_A @ sk_B)))
% 0.37/0.55         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['6', '10'])).
% 0.37/0.55  thf(d1_tarski, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.37/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.37/0.55  thf('12', plain,
% 0.37/0.55      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X9 @ X8) | ((X9) = (X6)) | ((X8) != (k1_tarski @ X6)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d1_tarski])).
% 0.37/0.55  thf('13', plain,
% 0.37/0.55      (![X6 : $i, X9 : $i]:
% 0.37/0.55         (((X9) = (X6)) | ~ (r2_hidden @ X9 @ (k1_tarski @ X6)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['12'])).
% 0.37/0.55  thf('14', plain,
% 0.37/0.55      ((((r2_hidden @ sk_A @ sk_B) | ((sk_A) = (sk_B))))
% 0.37/0.55         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['11', '13'])).
% 0.37/0.55  thf('15', plain,
% 0.37/0.55      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.55      inference('split', [status(esa)], ['0'])).
% 0.37/0.55  thf('16', plain,
% 0.37/0.55      ((((sk_A) = (sk_B)))
% 0.37/0.55         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.37/0.55             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['14', '15'])).
% 0.37/0.55  thf('17', plain, ((((sk_A) != (sk_B))) <= (~ (((sk_A) = (sk_B))))),
% 0.37/0.55      inference('split', [status(esa)], ['3'])).
% 0.37/0.55  thf('18', plain,
% 0.37/0.55      ((((sk_A) != (sk_A)))
% 0.37/0.55         <= (~ (((sk_A) = (sk_B))) & 
% 0.37/0.55             ~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.37/0.55             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.37/0.55  thf('19', plain,
% 0.37/0.55      (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) | 
% 0.37/0.55       ((r2_hidden @ sk_A @ sk_B)) | (((sk_A) = (sk_B)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['18'])).
% 0.37/0.55  thf('20', plain, (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.37/0.55      inference('sat_resolution*', [status(thm)], ['2', '4', '19'])).
% 0.37/0.55  thf('21', plain, (~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))),
% 0.37/0.55      inference('simpl_trail', [status(thm)], ['1', '20'])).
% 0.37/0.55  thf('22', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 0.37/0.55      inference('split', [status(esa)], ['5'])).
% 0.37/0.55  thf('23', plain,
% 0.37/0.55      (![X11 : $i]:
% 0.37/0.55         ((k1_ordinal1 @ X11) = (k2_xboole_0 @ X11 @ (k1_tarski @ X11)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.37/0.55  thf('24', plain,
% 0.37/0.55      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.55      inference('split', [status(esa)], ['5'])).
% 0.37/0.55  thf('25', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X0 @ X3)
% 0.37/0.55          | (r2_hidden @ X0 @ X2)
% 0.37/0.55          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.37/0.55  thf('26', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.37/0.55         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 0.37/0.55      inference('simplify', [status(thm)], ['25'])).
% 0.37/0.55  thf('27', plain,
% 0.37/0.55      ((![X0 : $i]: (r2_hidden @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))
% 0.37/0.55         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['24', '26'])).
% 0.37/0.55  thf('28', plain,
% 0.37/0.55      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.37/0.55         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['23', '27'])).
% 0.37/0.55  thf('29', plain,
% 0.37/0.55      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.37/0.55         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.37/0.55      inference('split', [status(esa)], ['0'])).
% 0.37/0.55  thf('30', plain,
% 0.37/0.55      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.37/0.55       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['28', '29'])).
% 0.37/0.55  thf('31', plain,
% 0.37/0.55      ((((sk_A) = (sk_B))) | ((r2_hidden @ sk_A @ sk_B)) | 
% 0.37/0.55       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.37/0.55      inference('split', [status(esa)], ['5'])).
% 0.37/0.55  thf('32', plain, ((((sk_A) = (sk_B)))),
% 0.37/0.55      inference('sat_resolution*', [status(thm)], ['2', '4', '19', '30', '31'])).
% 0.37/0.55  thf('33', plain, (((sk_A) = (sk_B))),
% 0.37/0.55      inference('simpl_trail', [status(thm)], ['22', '32'])).
% 0.37/0.55  thf('34', plain, (~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A))),
% 0.37/0.55      inference('demod', [status(thm)], ['21', '33'])).
% 0.37/0.55  thf('35', plain,
% 0.37/0.55      (![X11 : $i]:
% 0.37/0.55         ((k1_ordinal1 @ X11) = (k2_xboole_0 @ X11 @ (k1_tarski @ X11)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.37/0.55  thf('36', plain,
% 0.37/0.55      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.37/0.55         (((X7) != (X6)) | (r2_hidden @ X7 @ X8) | ((X8) != (k1_tarski @ X6)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d1_tarski])).
% 0.37/0.55  thf('37', plain, (![X6 : $i]: (r2_hidden @ X6 @ (k1_tarski @ X6))),
% 0.37/0.55      inference('simplify', [status(thm)], ['36'])).
% 0.37/0.55  thf('38', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X0 @ X1)
% 0.37/0.55          | (r2_hidden @ X0 @ X2)
% 0.37/0.55          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.37/0.55  thf('39', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.37/0.55         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.37/0.55      inference('simplify', [status(thm)], ['38'])).
% 0.37/0.55  thf('40', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['37', '39'])).
% 0.37/0.55  thf('41', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_ordinal1 @ X0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['35', '40'])).
% 0.37/0.55  thf('42', plain, ($false), inference('demod', [status(thm)], ['34', '41'])).
% 0.37/0.55  
% 0.37/0.55  % SZS output end Refutation
% 0.37/0.55  
% 0.37/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
