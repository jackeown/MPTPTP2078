%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KwbTZTWA6o

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 319 expanded)
%              Number of leaves         :    9 (  78 expanded)
%              Depth                    :   15
%              Number of atoms          :  421 (2967 expanded)
%              Number of equality atoms :   66 ( 498 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
   <= ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_A )
   <= ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
      & ( sk_A
        = ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( sk_A
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( X8
        = ( k2_tarski @ X6 @ X7 ) )
      | ( X8
        = ( k1_tarski @ X7 ) )
      | ( X8
        = ( k1_tarski @ X6 ) )
      | ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ ( k2_tarski @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_A
        = ( k1_tarski @ sk_B ) )
      | ( sk_A
        = ( k2_tarski @ sk_B @ sk_B ) ) )
   <= ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('14',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_A
        = ( k1_tarski @ sk_B ) )
      | ( sk_A
        = ( k1_tarski @ sk_B ) ) )
   <= ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( sk_A
        = ( k1_tarski @ sk_B ) )
      | ( sk_A = k1_xboole_0 ) )
   <= ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('17',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('19',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ ( k2_tarski @ X6 @ X9 ) )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('20',plain,(
    ! [X6: $i,X9: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k2_tarski @ X6 @ X9 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','20'])).

thf('22',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('23',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('24',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ sk_B ) )
   <= ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['17','25'])).

thf('27',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['16','26'])).

thf('28',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
   <= ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['15','27'])).

thf('29',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
   <= ( sk_A
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('30',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A
       != ( k1_tarski @ sk_B ) )
      & ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['6','31'])).

thf('33',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('34',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('35',plain,
    ( sk_A
    = ( k1_tarski @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['17','33','6','31','34'])).

thf('36',plain,(
    ~ ( r1_tarski @ sk_A @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['4','32','35'])).

thf('37',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
   <= ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,
    ( sk_A
    = ( k1_tarski @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['17','33','6','31','34'])).

thf('39',plain,
    ( sk_A
    = ( k1_tarski @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('41',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ ( k2_tarski @ X6 @ X9 ) )
      | ( X8
       != ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('42',plain,(
    ! [X6: $i,X9: $i] :
      ( r1_tarski @ ( k1_tarski @ X6 ) @ ( k2_tarski @ X6 @ X9 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','42'])).

thf('44',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup+',[status(thm)],['39','43'])).

thf('45',plain,
    ( sk_A
    = ( k1_tarski @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['37','38'])).

thf('46',plain,(
    r1_tarski @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['36','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KwbTZTWA6o
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:11:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 59 iterations in 0.022s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(t39_zfmisc_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.21/0.48       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i]:
% 0.21/0.48        ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.21/0.48          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t39_zfmisc_1])).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      ((((sk_A) = (k1_tarski @ sk_B))
% 0.21/0.48        | ((sk_A) = (k1_xboole_0))
% 0.21/0.48        | (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      ((((sk_A) = (k1_tarski @ sk_B))) <= ((((sk_A) = (k1_tarski @ sk_B))))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      ((((sk_A) != (k1_xboole_0)) | ~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      ((~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))
% 0.21/0.48         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.48      inference('split', [status(esa)], ['2'])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      ((~ (r1_tarski @ sk_A @ sk_A))
% 0.21/0.48         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))) & 
% 0.21/0.48             (((sk_A) = (k1_tarski @ sk_B))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '3'])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      ((((sk_A) != (k1_tarski @ sk_B))
% 0.21/0.48        | ~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))) | 
% 0.21/0.48       ~ (((sk_A) = (k1_tarski @ sk_B)))),
% 0.21/0.48      inference('split', [status(esa)], ['5'])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))
% 0.21/0.48         <= (((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf(t69_enumset1, axiom,
% 0.21/0.48    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.48  thf('8', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.48  thf(l45_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.21/0.48       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.21/0.48            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.48         (((X8) = (k2_tarski @ X6 @ X7))
% 0.21/0.48          | ((X8) = (k1_tarski @ X7))
% 0.21/0.48          | ((X8) = (k1_tarski @ X6))
% 0.21/0.48          | ((X8) = (k1_xboole_0))
% 0.21/0.48          | ~ (r1_tarski @ X8 @ (k2_tarski @ X6 @ X7)))),
% 0.21/0.48      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.21/0.48          | ((X1) = (k1_xboole_0))
% 0.21/0.48          | ((X1) = (k1_tarski @ X0))
% 0.21/0.48          | ((X1) = (k1_tarski @ X0))
% 0.21/0.48          | ((X1) = (k2_tarski @ X0 @ X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (((X1) = (k2_tarski @ X0 @ X0))
% 0.21/0.48          | ((X1) = (k1_tarski @ X0))
% 0.21/0.48          | ((X1) = (k1_xboole_0))
% 0.21/0.48          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (((((sk_A) = (k1_xboole_0))
% 0.21/0.48         | ((sk_A) = (k1_tarski @ sk_B))
% 0.21/0.48         | ((sk_A) = (k2_tarski @ sk_B @ sk_B))))
% 0.21/0.48         <= (((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['7', '11'])).
% 0.21/0.48  thf('13', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (((((sk_A) = (k1_xboole_0))
% 0.21/0.48         | ((sk_A) = (k1_tarski @ sk_B))
% 0.21/0.48         | ((sk_A) = (k1_tarski @ sk_B))))
% 0.21/0.48         <= (((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.48      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (((((sk_A) = (k1_tarski @ sk_B)) | ((sk_A) = (k1_xboole_0))))
% 0.21/0.48         <= (((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.48      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.21/0.48      inference('split', [status(esa)], ['2'])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.21/0.48       ~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.48      inference('split', [status(esa)], ['2'])).
% 0.21/0.48  thf('18', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.21/0.48         ((r1_tarski @ X8 @ (k2_tarski @ X6 @ X9)) | ((X8) != (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      (![X6 : $i, X9 : $i]: (r1_tarski @ k1_xboole_0 @ (k2_tarski @ X6 @ X9))),
% 0.21/0.48      inference('simplify', [status(thm)], ['19'])).
% 0.21/0.48  thf('21', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0))),
% 0.21/0.48      inference('sup+', [status(thm)], ['18', '20'])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      ((~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))
% 0.21/0.48         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.48      inference('split', [status(esa)], ['2'])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      ((~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ sk_B)))
% 0.21/0.48         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))) & 
% 0.21/0.48             (((sk_A) = (k1_xboole_0))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      (((r1_tarski @ sk_A @ (k1_tarski @ sk_B))) | ~ (((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['21', '24'])).
% 0.21/0.48  thf('26', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['17', '25'])).
% 0.21/0.48  thf('27', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['16', '26'])).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      ((((sk_A) = (k1_tarski @ sk_B)))
% 0.21/0.48         <= (((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['15', '27'])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      ((((sk_A) != (k1_tarski @ sk_B))) <= (~ (((sk_A) = (k1_tarski @ sk_B))))),
% 0.21/0.48      inference('split', [status(esa)], ['5'])).
% 0.21/0.48  thf('30', plain,
% 0.21/0.48      ((((sk_A) != (sk_A)))
% 0.21/0.48         <= (~ (((sk_A) = (k1_tarski @ sk_B))) & 
% 0.21/0.48             ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.48  thf('31', plain,
% 0.21/0.48      ((((sk_A) = (k1_tarski @ sk_B))) | 
% 0.21/0.48       ~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['30'])).
% 0.21/0.48  thf('32', plain, (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['6', '31'])).
% 0.21/0.48  thf('33', plain,
% 0.21/0.48      (~ (((sk_A) = (k1_xboole_0))) | ((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['21', '24'])).
% 0.21/0.48  thf('34', plain,
% 0.21/0.48      ((((sk_A) = (k1_tarski @ sk_B))) | 
% 0.21/0.48       ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))) | (((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('35', plain, ((((sk_A) = (k1_tarski @ sk_B)))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['17', '33', '6', '31', '34'])).
% 0.21/0.48  thf('36', plain, (~ (r1_tarski @ sk_A @ sk_A)),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['4', '32', '35'])).
% 0.21/0.48  thf('37', plain,
% 0.21/0.48      ((((sk_A) = (k1_tarski @ sk_B))) <= ((((sk_A) = (k1_tarski @ sk_B))))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('38', plain, ((((sk_A) = (k1_tarski @ sk_B)))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['17', '33', '6', '31', '34'])).
% 0.21/0.48  thf('39', plain, (((sk_A) = (k1_tarski @ sk_B))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['37', '38'])).
% 0.21/0.48  thf('40', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.48  thf('41', plain,
% 0.21/0.48      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.21/0.48         ((r1_tarski @ X8 @ (k2_tarski @ X6 @ X9)) | ((X8) != (k1_tarski @ X6)))),
% 0.21/0.48      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.21/0.48  thf('42', plain,
% 0.21/0.48      (![X6 : $i, X9 : $i]:
% 0.21/0.48         (r1_tarski @ (k1_tarski @ X6) @ (k2_tarski @ X6 @ X9))),
% 0.21/0.48      inference('simplify', [status(thm)], ['41'])).
% 0.21/0.48  thf('43', plain,
% 0.21/0.48      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.21/0.48      inference('sup+', [status(thm)], ['40', '42'])).
% 0.21/0.48  thf('44', plain, ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))),
% 0.21/0.48      inference('sup+', [status(thm)], ['39', '43'])).
% 0.21/0.48  thf('45', plain, (((sk_A) = (k1_tarski @ sk_B))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['37', '38'])).
% 0.21/0.48  thf('46', plain, ((r1_tarski @ sk_A @ sk_A)),
% 0.21/0.48      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.48  thf('47', plain, ($false), inference('demod', [status(thm)], ['36', '46'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
