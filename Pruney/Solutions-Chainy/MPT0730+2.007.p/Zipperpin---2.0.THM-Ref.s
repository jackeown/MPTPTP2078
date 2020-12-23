%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dspxXgp3Ci

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:44 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   58 (  89 expanded)
%              Number of leaves         :   12 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :  431 ( 731 expanded)
%              Number of equality atoms :   41 (  71 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ( ( sk_A != sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_A != sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('2',plain,(
    ! [X62: $i] :
      ( ( k1_ordinal1 @ X62 )
      = ( k2_xboole_0 @ X62 @ ( k1_tarski @ X62 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('3',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X7 != X6 )
      | ( r2_hidden @ X7 @ X8 )
      | ( X8
       != ( k2_tarski @ X9 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('5',plain,(
    ! [X6: $i,X9: $i] :
      ( r2_hidden @ X6 @ ( k2_tarski @ X9 @ X6 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','9'])).

thf('11',plain,
    ( ( sk_A = sk_B )
    | ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,
    ( ( sk_A != sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['13'])).

thf('18',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['11'])).

thf('19',plain,(
    ! [X62: $i] :
      ( ( k1_ordinal1 @ X62 )
      = ( k2_xboole_0 @ X62 @ ( k1_tarski @ X62 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('20',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('21',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('25',plain,(
    ! [X6: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ( X10 = X9 )
      | ( X10 = X6 )
      | ( X8
       != ( k2_tarski @ X9 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('26',plain,(
    ! [X6: $i,X9: $i,X10: $i] :
      ( ( X10 = X6 )
      | ( X10 = X9 )
      | ~ ( r2_hidden @ X10 @ ( k2_tarski @ X9 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ( sk_A = sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['13'])).

thf('31',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_A != sk_B )
   <= ( sk_A != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != sk_B )
      & ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
    | ( sk_A = sk_B ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X62: $i] :
      ( ( k1_ordinal1 @ X62 )
      = ( k2_xboole_0 @ X62 @ ( k1_tarski @ X62 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('36',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['11'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['35','39'])).

thf('41',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['13'])).

thf('42',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
    | ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['11'])).

thf('44',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','16','17','34','42','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dspxXgp3Ci
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:19:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 0.22/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.55  % Solved by: fo/fo7.sh
% 0.22/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.55  % done 173 iterations in 0.091s
% 0.22/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.55  % SZS output start Refutation
% 0.22/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.55  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.22/0.55  thf(t13_ordinal1, conjecture,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.22/0.55       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.22/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.55    (~( ![A:$i,B:$i]:
% 0.22/0.55        ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.22/0.55          ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ) )),
% 0.22/0.55    inference('cnf.neg', [status(esa)], [t13_ordinal1])).
% 0.22/0.55  thf('0', plain,
% 0.22/0.55      ((((sk_A) != (sk_B)) | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('1', plain,
% 0.22/0.55      (~ (((sk_A) = (sk_B))) | ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.22/0.55      inference('split', [status(esa)], ['0'])).
% 0.22/0.55  thf(d1_ordinal1, axiom,
% 0.22/0.55    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.22/0.55  thf('2', plain,
% 0.22/0.55      (![X62 : $i]:
% 0.22/0.55         ((k1_ordinal1 @ X62) = (k2_xboole_0 @ X62 @ (k1_tarski @ X62)))),
% 0.22/0.55      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.22/0.55  thf(t69_enumset1, axiom,
% 0.22/0.55    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.55  thf('3', plain, (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.22/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.55  thf(d2_tarski, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i]:
% 0.22/0.55     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.22/0.55       ( ![D:$i]:
% 0.22/0.55         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.22/0.55  thf('4', plain,
% 0.22/0.55      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.55         (((X7) != (X6))
% 0.22/0.55          | (r2_hidden @ X7 @ X8)
% 0.22/0.55          | ((X8) != (k2_tarski @ X9 @ X6)))),
% 0.22/0.55      inference('cnf', [status(esa)], [d2_tarski])).
% 0.22/0.55  thf('5', plain,
% 0.22/0.55      (![X6 : $i, X9 : $i]: (r2_hidden @ X6 @ (k2_tarski @ X9 @ X6))),
% 0.22/0.55      inference('simplify', [status(thm)], ['4'])).
% 0.22/0.55  thf('6', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.22/0.55      inference('sup+', [status(thm)], ['3', '5'])).
% 0.22/0.55  thf(d3_xboole_0, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i]:
% 0.22/0.55     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.22/0.55       ( ![D:$i]:
% 0.22/0.55         ( ( r2_hidden @ D @ C ) <=>
% 0.22/0.55           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.22/0.55  thf('7', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.55         (~ (r2_hidden @ X0 @ X1)
% 0.22/0.55          | (r2_hidden @ X0 @ X2)
% 0.22/0.55          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.22/0.55      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.22/0.55  thf('8', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.22/0.55         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.22/0.55      inference('simplify', [status(thm)], ['7'])).
% 0.22/0.55  thf('9', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['6', '8'])).
% 0.22/0.55  thf('10', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_ordinal1 @ X0))),
% 0.22/0.55      inference('sup+', [status(thm)], ['2', '9'])).
% 0.22/0.55  thf('11', plain,
% 0.22/0.55      ((((sk_A) = (sk_B))
% 0.22/0.55        | (r2_hidden @ sk_A @ sk_B)
% 0.22/0.55        | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('12', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 0.22/0.55      inference('split', [status(esa)], ['11'])).
% 0.22/0.55  thf('13', plain,
% 0.22/0.55      ((~ (r2_hidden @ sk_A @ sk_B)
% 0.22/0.55        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('14', plain,
% 0.22/0.55      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.22/0.55         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.22/0.55      inference('split', [status(esa)], ['13'])).
% 0.22/0.55  thf('15', plain,
% 0.22/0.55      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 0.22/0.55         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.22/0.55             (((sk_A) = (sk_B))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['12', '14'])).
% 0.22/0.55  thf('16', plain,
% 0.22/0.55      (~ (((sk_A) = (sk_B))) | ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['10', '15'])).
% 0.22/0.55  thf('17', plain,
% 0.22/0.55      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.22/0.55       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.22/0.55      inference('split', [status(esa)], ['13'])).
% 0.22/0.55  thf('18', plain,
% 0.22/0.55      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.22/0.55         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.22/0.55      inference('split', [status(esa)], ['11'])).
% 0.22/0.55  thf('19', plain,
% 0.22/0.55      (![X62 : $i]:
% 0.22/0.55         ((k1_ordinal1 @ X62) = (k2_xboole_0 @ X62 @ (k1_tarski @ X62)))),
% 0.22/0.55      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.22/0.55  thf('20', plain,
% 0.22/0.55      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.55         (~ (r2_hidden @ X4 @ X2)
% 0.22/0.55          | (r2_hidden @ X4 @ X3)
% 0.22/0.55          | (r2_hidden @ X4 @ X1)
% 0.22/0.55          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.22/0.55      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.22/0.55  thf('21', plain,
% 0.22/0.55      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.22/0.55         ((r2_hidden @ X4 @ X1)
% 0.38/0.55          | (r2_hidden @ X4 @ X3)
% 0.38/0.55          | ~ (r2_hidden @ X4 @ (k2_xboole_0 @ X3 @ X1)))),
% 0.38/0.55      inference('simplify', [status(thm)], ['20'])).
% 0.38/0.55  thf('22', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.38/0.55          | (r2_hidden @ X1 @ X0)
% 0.38/0.55          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['19', '21'])).
% 0.38/0.55  thf('23', plain,
% 0.38/0.55      ((((r2_hidden @ sk_A @ (k1_tarski @ sk_B)) | (r2_hidden @ sk_A @ sk_B)))
% 0.38/0.55         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['18', '22'])).
% 0.38/0.55  thf('24', plain,
% 0.38/0.55      (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.38/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.38/0.55  thf('25', plain,
% 0.38/0.55      (![X6 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.38/0.55         (~ (r2_hidden @ X10 @ X8)
% 0.38/0.55          | ((X10) = (X9))
% 0.38/0.55          | ((X10) = (X6))
% 0.38/0.55          | ((X8) != (k2_tarski @ X9 @ X6)))),
% 0.38/0.55      inference('cnf', [status(esa)], [d2_tarski])).
% 0.38/0.55  thf('26', plain,
% 0.38/0.55      (![X6 : $i, X9 : $i, X10 : $i]:
% 0.38/0.55         (((X10) = (X6))
% 0.38/0.55          | ((X10) = (X9))
% 0.38/0.55          | ~ (r2_hidden @ X10 @ (k2_tarski @ X9 @ X6)))),
% 0.38/0.55      inference('simplify', [status(thm)], ['25'])).
% 0.38/0.55  thf('27', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['24', '26'])).
% 0.38/0.55  thf('28', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.38/0.55      inference('simplify', [status(thm)], ['27'])).
% 0.38/0.55  thf('29', plain,
% 0.38/0.55      ((((r2_hidden @ sk_A @ sk_B) | ((sk_A) = (sk_B))))
% 0.38/0.55         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['23', '28'])).
% 0.38/0.55  thf('30', plain,
% 0.38/0.55      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.38/0.55      inference('split', [status(esa)], ['13'])).
% 0.38/0.55  thf('31', plain,
% 0.38/0.55      ((((sk_A) = (sk_B)))
% 0.38/0.55         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.38/0.55             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['29', '30'])).
% 0.38/0.55  thf('32', plain, ((((sk_A) != (sk_B))) <= (~ (((sk_A) = (sk_B))))),
% 0.38/0.55      inference('split', [status(esa)], ['0'])).
% 0.38/0.55  thf('33', plain,
% 0.38/0.55      ((((sk_A) != (sk_A)))
% 0.38/0.55         <= (~ (((sk_A) = (sk_B))) & 
% 0.38/0.55             ~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.38/0.55             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['31', '32'])).
% 0.38/0.55  thf('34', plain,
% 0.38/0.55      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.38/0.55       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) | (((sk_A) = (sk_B)))),
% 0.38/0.55      inference('simplify', [status(thm)], ['33'])).
% 0.38/0.55  thf('35', plain,
% 0.38/0.55      (![X62 : $i]:
% 0.38/0.55         ((k1_ordinal1 @ X62) = (k2_xboole_0 @ X62 @ (k1_tarski @ X62)))),
% 0.38/0.55      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.38/0.55  thf('36', plain,
% 0.38/0.55      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.38/0.55      inference('split', [status(esa)], ['11'])).
% 0.38/0.55  thf('37', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.55         (~ (r2_hidden @ X0 @ X3)
% 0.38/0.55          | (r2_hidden @ X0 @ X2)
% 0.38/0.55          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.38/0.55      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.38/0.55  thf('38', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.38/0.55         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 0.38/0.55      inference('simplify', [status(thm)], ['37'])).
% 0.38/0.55  thf('39', plain,
% 0.38/0.55      ((![X0 : $i]: (r2_hidden @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))
% 0.38/0.55         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['36', '38'])).
% 0.38/0.55  thf('40', plain,
% 0.38/0.55      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.38/0.55         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.38/0.55      inference('sup+', [status(thm)], ['35', '39'])).
% 0.38/0.55  thf('41', plain,
% 0.38/0.55      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.38/0.55         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.38/0.55      inference('split', [status(esa)], ['13'])).
% 0.38/0.55  thf('42', plain,
% 0.38/0.55      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.38/0.55       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['40', '41'])).
% 0.38/0.55  thf('43', plain,
% 0.38/0.55      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.38/0.55       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) | (((sk_A) = (sk_B)))),
% 0.38/0.55      inference('split', [status(esa)], ['11'])).
% 0.38/0.56  thf('44', plain, ($false),
% 0.38/0.56      inference('sat_resolution*', [status(thm)],
% 0.38/0.56                ['1', '16', '17', '34', '42', '43'])).
% 0.38/0.56  
% 0.38/0.56  % SZS output end Refutation
% 0.38/0.56  
% 0.38/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
