%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Kd6r0DVRKN

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   44 (  72 expanded)
%              Number of leaves         :    9 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :  381 ( 707 expanded)
%              Number of equality atoms :   28 (  54 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t64_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( A != C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_zfmisc_1])).

thf('0',plain,
    ( ( sk_A != sk_C_1 )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_A != sk_C_1 )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( X7 != X6 )
      | ( r2_hidden @ X7 @ X8 )
      | ( X8
       != ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('3',plain,(
    ! [X6: $i] :
      ( r2_hidden @ X6 @ ( k1_tarski @ X6 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,
    ( ( sk_A = sk_C_1 )
    | ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( sk_A = sk_C_1 )
   <= ( sk_A = sk_C_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( sk_A = sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['5','7'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('9',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('10',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
   <= ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( sk_A = sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,
    ( ( sk_A != sk_C_1 )
    | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['3','11'])).

thf('13',plain,
    ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['6'])).

thf('14',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('15',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('18',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
    | ( sk_A = sk_C_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('20',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['6'])).

thf('21',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ X0 )
        | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
   <= ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('26',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C_1 ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X8 )
      | ( X9 = X6 )
      | ( X8
       != ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('28',plain,(
    ! [X6: $i,X9: $i] :
      ( ( X9 = X6 )
      | ~ ( r2_hidden @ X9 @ ( k1_tarski @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( sk_A = sk_C_1 )
   <= ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,
    ( ( sk_A != sk_C_1 )
   <= ( sk_A != sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != sk_C_1 )
      & ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
    | ( sk_A = sk_C_1 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','12','18','19','20','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Kd6r0DVRKN
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:59:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 78 iterations in 0.130s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(t64_zfmisc_1, conjecture,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.21/0.55       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.55        ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.21/0.55          ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t64_zfmisc_1])).
% 0.21/0.55  thf('0', plain,
% 0.21/0.55      ((((sk_A) != (sk_C_1))
% 0.21/0.55        | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('1', plain,
% 0.21/0.55      (~ (((sk_A) = (sk_C_1))) | 
% 0.21/0.55       ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf(d1_tarski, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.55         (((X7) != (X6)) | (r2_hidden @ X7 @ X8) | ((X8) != (k1_tarski @ X6)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.55  thf('3', plain, (![X6 : $i]: (r2_hidden @ X6 @ (k1_tarski @ X6))),
% 0.21/0.55      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      ((((sk_A) = (sk_C_1))
% 0.21/0.55        | ~ (r2_hidden @ sk_A @ sk_B)
% 0.21/0.55        | ~ (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('5', plain, ((((sk_A) = (sk_C_1))) <= ((((sk_A) = (sk_C_1))))),
% 0.21/0.55      inference('split', [status(esa)], ['4'])).
% 0.21/0.55  thf('6', plain,
% 0.21/0.55      (((r2_hidden @ sk_A @ sk_B)
% 0.21/0.55        | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('7', plain,
% 0.21/0.55      (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))
% 0.21/0.55         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 0.21/0.55      inference('split', [status(esa)], ['6'])).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.21/0.55         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) & 
% 0.21/0.55             (((sk_A) = (sk_C_1))))),
% 0.21/0.55      inference('sup+', [status(thm)], ['5', '7'])).
% 0.21/0.55  thf(d5_xboole_0, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.21/0.55       ( ![D:$i]:
% 0.21/0.55         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.55           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.21/0.55  thf('9', plain,
% 0.21/0.55      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X4 @ X3)
% 0.21/0.55          | ~ (r2_hidden @ X4 @ X2)
% 0.21/0.55          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.55  thf('10', plain,
% 0.21/0.55      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X4 @ X2)
% 0.21/0.55          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      ((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))
% 0.21/0.55         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) & 
% 0.21/0.55             (((sk_A) = (sk_C_1))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['8', '10'])).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      (~ (((sk_A) = (sk_C_1))) | 
% 0.21/0.55       ~ ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['3', '11'])).
% 0.21/0.55  thf('13', plain,
% 0.21/0.55      (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))
% 0.21/0.55         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 0.21/0.55      inference('split', [status(esa)], ['6'])).
% 0.21/0.55  thf('14', plain,
% 0.21/0.55      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X4 @ X3)
% 0.21/0.55          | (r2_hidden @ X4 @ X1)
% 0.21/0.55          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.55  thf('15', plain,
% 0.21/0.55      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.21/0.55         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.55  thf('16', plain,
% 0.21/0.55      (((r2_hidden @ sk_A @ sk_B))
% 0.21/0.55         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['13', '15'])).
% 0.21/0.55  thf('17', plain,
% 0.21/0.55      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.21/0.55      inference('split', [status(esa)], ['4'])).
% 0.21/0.55  thf('18', plain,
% 0.21/0.55      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.21/0.55       ~ ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.55  thf('19', plain,
% 0.21/0.55      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.21/0.55       ~ ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) | 
% 0.21/0.55       (((sk_A) = (sk_C_1)))),
% 0.21/0.55      inference('split', [status(esa)], ['4'])).
% 0.21/0.55  thf('20', plain,
% 0.21/0.55      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.21/0.55       ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))),
% 0.21/0.55      inference('split', [status(esa)], ['6'])).
% 0.21/0.55  thf('21', plain,
% 0.21/0.55      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.21/0.55      inference('split', [status(esa)], ['6'])).
% 0.21/0.55  thf('22', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.55          | (r2_hidden @ X0 @ X2)
% 0.21/0.55          | (r2_hidden @ X0 @ X3)
% 0.21/0.55          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.55  thf('23', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.21/0.55          | (r2_hidden @ X0 @ X2)
% 0.21/0.55          | ~ (r2_hidden @ X0 @ X1))),
% 0.21/0.55      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.55  thf('24', plain,
% 0.21/0.55      ((![X0 : $i]:
% 0.21/0.55          ((r2_hidden @ sk_A @ X0)
% 0.21/0.55           | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ X0))))
% 0.21/0.55         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['21', '23'])).
% 0.21/0.55  thf('25', plain,
% 0.21/0.55      ((~ (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))
% 0.21/0.55         <= (~
% 0.21/0.55             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 0.21/0.55      inference('split', [status(esa)], ['4'])).
% 0.21/0.55  thf('26', plain,
% 0.21/0.55      (((r2_hidden @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.21/0.55         <= (~
% 0.21/0.55             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) & 
% 0.21/0.55             ((r2_hidden @ sk_A @ sk_B)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.55  thf('27', plain,
% 0.21/0.55      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X9 @ X8) | ((X9) = (X6)) | ((X8) != (k1_tarski @ X6)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.55  thf('28', plain,
% 0.21/0.55      (![X6 : $i, X9 : $i]:
% 0.21/0.55         (((X9) = (X6)) | ~ (r2_hidden @ X9 @ (k1_tarski @ X6)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['27'])).
% 0.21/0.55  thf('29', plain,
% 0.21/0.55      ((((sk_A) = (sk_C_1)))
% 0.21/0.55         <= (~
% 0.21/0.55             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) & 
% 0.21/0.55             ((r2_hidden @ sk_A @ sk_B)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['26', '28'])).
% 0.21/0.55  thf('30', plain, ((((sk_A) != (sk_C_1))) <= (~ (((sk_A) = (sk_C_1))))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf('31', plain,
% 0.21/0.55      ((((sk_A) != (sk_A)))
% 0.21/0.55         <= (~ (((sk_A) = (sk_C_1))) & 
% 0.21/0.55             ~
% 0.21/0.55             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) & 
% 0.21/0.55             ((r2_hidden @ sk_A @ sk_B)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.55  thf('32', plain,
% 0.21/0.55      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.21/0.55       ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) | 
% 0.21/0.55       (((sk_A) = (sk_C_1)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['31'])).
% 0.21/0.55  thf('33', plain, ($false),
% 0.21/0.55      inference('sat_resolution*', [status(thm)],
% 0.21/0.55                ['1', '12', '18', '19', '20', '32'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
