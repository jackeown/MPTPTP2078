%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QbYMQbDe8O

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:12 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   49 (  97 expanded)
%              Number of leaves         :   13 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :  305 ( 749 expanded)
%              Number of equality atoms :   37 ( 103 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t39_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
      <=> ( ( A = k1_xboole_0 )
          | ( A
            = ( k1_tarski @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_zfmisc_1])).

thf('0',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('3',plain,(
    ! [X10: $i] :
      ( r1_xboole_0 @ X10 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('4',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X20 ) @ X21 )
      | ~ ( r2_hidden @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ sk_B ) )
   <= ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('12',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,
    ( ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('15',plain,(
    ! [X22: $i,X23: $i] :
      ( ( X23
        = ( k1_tarski @ X22 ) )
      | ( X23 = k1_xboole_0 )
      | ~ ( r1_tarski @ X23 @ ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('16',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_A
        = ( k1_tarski @ sk_B ) ) )
   <= ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,
    ( ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('19',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['1','18'])).

thf('20',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['17','19'])).

thf('21',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
   <= ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['16','20'])).

thf('22',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
   <= ( sk_A
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['12'])).

thf('23',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A
       != ( k1_tarski @ sk_B ) )
      & ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['7'])).

thf('26',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
   <= ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf('31',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_A )
   <= ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
      & ( sk_A
        = ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','11','13','24','25','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.10  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QbYMQbDe8O
% 0.11/0.31  % Computer   : n015.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 10:37:53 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.11/0.31  % Running portfolio for 600 s
% 0.11/0.31  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.11/0.31  % Number of cores: 8
% 0.11/0.31  % Python version: Python 3.6.8
% 0.11/0.31  % Running in FO mode
% 0.17/0.38  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.17/0.38  % Solved by: fo/fo7.sh
% 0.17/0.38  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.17/0.38  % done 83 iterations in 0.013s
% 0.17/0.38  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.17/0.38  % SZS output start Refutation
% 0.17/0.38  thf(sk_A_type, type, sk_A: $i).
% 0.17/0.38  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.17/0.38  thf(sk_B_type, type, sk_B: $i).
% 0.17/0.38  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.17/0.38  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.17/0.38  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.17/0.38  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.17/0.38  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.17/0.38  thf(t39_zfmisc_1, conjecture,
% 0.17/0.38    (![A:$i,B:$i]:
% 0.17/0.38     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.17/0.38       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.17/0.38  thf(zf_stmt_0, negated_conjecture,
% 0.17/0.38    (~( ![A:$i,B:$i]:
% 0.17/0.38        ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.17/0.38          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ) )),
% 0.17/0.38    inference('cnf.neg', [status(esa)], [t39_zfmisc_1])).
% 0.17/0.38  thf('0', plain,
% 0.17/0.38      ((((sk_A) != (k1_xboole_0)) | ~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.17/0.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.38  thf('1', plain,
% 0.17/0.38      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.17/0.38       ~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.17/0.38      inference('split', [status(esa)], ['0'])).
% 0.17/0.38  thf(d3_tarski, axiom,
% 0.17/0.38    (![A:$i,B:$i]:
% 0.17/0.38     ( ( r1_tarski @ A @ B ) <=>
% 0.17/0.38       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.17/0.38  thf('2', plain,
% 0.17/0.38      (![X1 : $i, X3 : $i]:
% 0.17/0.38         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.17/0.38      inference('cnf', [status(esa)], [d3_tarski])).
% 0.17/0.38  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.17/0.38  thf('3', plain, (![X10 : $i]: (r1_xboole_0 @ X10 @ k1_xboole_0)),
% 0.17/0.38      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.17/0.38  thf(l24_zfmisc_1, axiom,
% 0.17/0.38    (![A:$i,B:$i]:
% 0.17/0.38     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.17/0.38  thf('4', plain,
% 0.17/0.38      (![X20 : $i, X21 : $i]:
% 0.17/0.38         (~ (r1_xboole_0 @ (k1_tarski @ X20) @ X21) | ~ (r2_hidden @ X20 @ X21))),
% 0.17/0.38      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.17/0.38  thf('5', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.17/0.38      inference('sup-', [status(thm)], ['3', '4'])).
% 0.17/0.38  thf('6', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.17/0.38      inference('sup-', [status(thm)], ['2', '5'])).
% 0.17/0.38  thf('7', plain,
% 0.17/0.38      ((((sk_A) = (k1_tarski @ sk_B))
% 0.17/0.38        | ((sk_A) = (k1_xboole_0))
% 0.17/0.38        | (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.17/0.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.38  thf('8', plain, ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.17/0.38      inference('split', [status(esa)], ['7'])).
% 0.17/0.38  thf('9', plain,
% 0.17/0.38      ((~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))
% 0.17/0.38         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.17/0.38      inference('split', [status(esa)], ['0'])).
% 0.17/0.38  thf('10', plain,
% 0.17/0.38      ((~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ sk_B)))
% 0.17/0.38         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))) & 
% 0.17/0.38             (((sk_A) = (k1_xboole_0))))),
% 0.17/0.38      inference('sup-', [status(thm)], ['8', '9'])).
% 0.17/0.38  thf('11', plain,
% 0.17/0.38      (~ (((sk_A) = (k1_xboole_0))) | ((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.17/0.38      inference('sup-', [status(thm)], ['6', '10'])).
% 0.17/0.38  thf('12', plain,
% 0.17/0.38      ((((sk_A) != (k1_tarski @ sk_B))
% 0.17/0.38        | ~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.17/0.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.38  thf('13', plain,
% 0.17/0.38      (~ (((sk_A) = (k1_tarski @ sk_B))) | 
% 0.17/0.38       ~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.17/0.38      inference('split', [status(esa)], ['12'])).
% 0.17/0.38  thf('14', plain,
% 0.17/0.38      (((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))
% 0.17/0.38         <= (((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.17/0.38      inference('split', [status(esa)], ['7'])).
% 0.17/0.38  thf(l3_zfmisc_1, axiom,
% 0.17/0.38    (![A:$i,B:$i]:
% 0.17/0.38     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.17/0.38       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.17/0.38  thf('15', plain,
% 0.17/0.38      (![X22 : $i, X23 : $i]:
% 0.17/0.38         (((X23) = (k1_tarski @ X22))
% 0.17/0.38          | ((X23) = (k1_xboole_0))
% 0.17/0.38          | ~ (r1_tarski @ X23 @ (k1_tarski @ X22)))),
% 0.17/0.38      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.17/0.38  thf('16', plain,
% 0.17/0.38      (((((sk_A) = (k1_xboole_0)) | ((sk_A) = (k1_tarski @ sk_B))))
% 0.17/0.38         <= (((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.17/0.38      inference('sup-', [status(thm)], ['14', '15'])).
% 0.17/0.38  thf('17', plain,
% 0.17/0.38      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.17/0.38      inference('split', [status(esa)], ['0'])).
% 0.17/0.38  thf('18', plain,
% 0.17/0.38      (((r1_tarski @ sk_A @ (k1_tarski @ sk_B))) | ~ (((sk_A) = (k1_xboole_0)))),
% 0.17/0.38      inference('sup-', [status(thm)], ['6', '10'])).
% 0.17/0.38  thf('19', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.17/0.38      inference('sat_resolution*', [status(thm)], ['1', '18'])).
% 0.17/0.38  thf('20', plain, (((sk_A) != (k1_xboole_0))),
% 0.17/0.38      inference('simpl_trail', [status(thm)], ['17', '19'])).
% 0.17/0.38  thf('21', plain,
% 0.17/0.38      ((((sk_A) = (k1_tarski @ sk_B)))
% 0.17/0.38         <= (((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.17/0.38      inference('simplify_reflect-', [status(thm)], ['16', '20'])).
% 0.17/0.38  thf('22', plain,
% 0.17/0.38      ((((sk_A) != (k1_tarski @ sk_B))) <= (~ (((sk_A) = (k1_tarski @ sk_B))))),
% 0.17/0.38      inference('split', [status(esa)], ['12'])).
% 0.17/0.38  thf('23', plain,
% 0.17/0.38      ((((sk_A) != (sk_A)))
% 0.17/0.38         <= (~ (((sk_A) = (k1_tarski @ sk_B))) & 
% 0.17/0.38             ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.17/0.38      inference('sup-', [status(thm)], ['21', '22'])).
% 0.17/0.38  thf('24', plain,
% 0.17/0.38      ((((sk_A) = (k1_tarski @ sk_B))) | 
% 0.17/0.38       ~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.17/0.38      inference('simplify', [status(thm)], ['23'])).
% 0.17/0.38  thf('25', plain,
% 0.17/0.38      ((((sk_A) = (k1_tarski @ sk_B))) | 
% 0.17/0.38       ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))) | (((sk_A) = (k1_xboole_0)))),
% 0.17/0.38      inference('split', [status(esa)], ['7'])).
% 0.17/0.38  thf('26', plain,
% 0.17/0.38      (![X1 : $i, X3 : $i]:
% 0.17/0.38         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.17/0.38      inference('cnf', [status(esa)], [d3_tarski])).
% 0.17/0.38  thf('27', plain,
% 0.17/0.38      (![X1 : $i, X3 : $i]:
% 0.17/0.38         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.17/0.38      inference('cnf', [status(esa)], [d3_tarski])).
% 0.17/0.38  thf('28', plain,
% 0.17/0.38      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.17/0.38      inference('sup-', [status(thm)], ['26', '27'])).
% 0.17/0.38  thf('29', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.17/0.38      inference('simplify', [status(thm)], ['28'])).
% 0.17/0.38  thf('30', plain,
% 0.17/0.38      ((((sk_A) = (k1_tarski @ sk_B))) <= ((((sk_A) = (k1_tarski @ sk_B))))),
% 0.17/0.38      inference('split', [status(esa)], ['7'])).
% 0.17/0.38  thf('31', plain,
% 0.17/0.38      ((~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))
% 0.17/0.38         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.17/0.38      inference('split', [status(esa)], ['0'])).
% 0.17/0.38  thf('32', plain,
% 0.17/0.38      ((~ (r1_tarski @ sk_A @ sk_A))
% 0.17/0.38         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))) & 
% 0.17/0.38             (((sk_A) = (k1_tarski @ sk_B))))),
% 0.17/0.38      inference('sup-', [status(thm)], ['30', '31'])).
% 0.17/0.38  thf('33', plain,
% 0.17/0.38      (~ (((sk_A) = (k1_tarski @ sk_B))) | 
% 0.17/0.38       ((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.17/0.38      inference('sup-', [status(thm)], ['29', '32'])).
% 0.17/0.38  thf('34', plain, ($false),
% 0.17/0.38      inference('sat_resolution*', [status(thm)],
% 0.17/0.38                ['1', '11', '13', '24', '25', '33'])).
% 0.17/0.38  
% 0.17/0.38  % SZS output end Refutation
% 0.17/0.38  
% 0.17/0.39  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
