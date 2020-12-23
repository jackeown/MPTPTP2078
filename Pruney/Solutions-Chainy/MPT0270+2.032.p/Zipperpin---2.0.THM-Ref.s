%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pnGsDBJUdj

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 181 expanded)
%              Number of leaves         :   17 (  60 expanded)
%              Depth                    :   18
%              Number of atoms          :  504 (1379 expanded)
%              Number of equality atoms :   61 ( 168 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X11: $i] :
      ( ( X11 = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('20',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('25',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('27',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = sk_B )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('28',plain,(
    ! [X60: $i,X61: $i] :
      ( ~ ( r2_hidden @ X60 @ X61 )
      | ( ( k4_xboole_0 @ X61 @ ( k1_tarski @ X60 ) )
       != X61 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('29',plain,
    ( ( ( sk_B != sk_B )
      | ~ ( r2_hidden @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','30'])).

thf('32',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','31'])).

thf('33',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','32'])).

thf('34',plain,(
    ! [X61: $i,X62: $i] :
      ( ( ( k4_xboole_0 @ X61 @ ( k1_tarski @ X62 ) )
        = X61 )
      | ( r2_hidden @ X62 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('35',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('40',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('46',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('47',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','31','46'])).

thf('48',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['45','47'])).

thf('49',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['44','48'])).

thf('50',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['33','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pnGsDBJUdj
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:27:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 228 iterations in 0.101s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.53  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(t67_zfmisc_1, conjecture,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.53       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i,B:$i]:
% 0.21/0.53        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.53          ( ~( r2_hidden @ A @ B ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t67_zfmisc_1])).
% 0.21/0.53  thf('0', plain,
% 0.21/0.53      ((~ (r2_hidden @ sk_A @ sk_B)
% 0.21/0.53        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.21/0.53      inference('split', [status(esa)], ['0'])).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.21/0.53       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('split', [status(esa)], ['0'])).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (((r2_hidden @ sk_A @ sk_B)
% 0.21/0.53        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.21/0.53      inference('split', [status(esa)], ['3'])).
% 0.21/0.53  thf(t17_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X9 : $i, X10 : $i]: (r1_tarski @ (k3_xboole_0 @ X9 @ X10) @ X9)),
% 0.21/0.53      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.21/0.53  thf(t3_xboole_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X11 : $i]:
% 0.21/0.53         (((X11) = (k1_xboole_0)) | ~ (r1_tarski @ X11 @ k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.53  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['7', '8'])).
% 0.21/0.53  thf(t100_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      (![X7 : $i, X8 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ X7 @ X8)
% 0.21/0.53           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.53  thf(t5_boole, axiom,
% 0.21/0.53    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.53  thf('12', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.21/0.53      inference('cnf', [status(esa)], [t5_boole])).
% 0.21/0.53  thf('13', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.53  thf(t48_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (![X12 : $i, X13 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.21/0.53           = (k3_xboole_0 @ X12 @ X13))),
% 0.21/0.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['13', '14'])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['7', '8'])).
% 0.21/0.53  thf('17', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.53      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))
% 0.21/0.53         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.53      inference('split', [status(esa)], ['0'])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (![X12 : $i, X13 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.21/0.53           = (k3_xboole_0 @ X12 @ X13))),
% 0.21/0.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.21/0.53          = (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))
% 0.21/0.53         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.53      inference('sup+', [status(thm)], ['18', '19'])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.21/0.53          = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.21/0.53         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.53      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      ((((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.21/0.53         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.53      inference('sup+', [status(thm)], ['17', '22'])).
% 0.21/0.53  thf('24', plain,
% 0.21/0.53      (![X7 : $i, X8 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ X7 @ X8)
% 0.21/0.53           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      ((((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.21/0.53          = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.21/0.53         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.53      inference('sup+', [status(thm)], ['23', '24'])).
% 0.21/0.53  thf('26', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.21/0.53      inference('cnf', [status(esa)], [t5_boole])).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      ((((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B)))
% 0.21/0.53         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.53      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.53  thf(t65_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.21/0.53       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      (![X60 : $i, X61 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X60 @ X61)
% 0.21/0.53          | ((k4_xboole_0 @ X61 @ (k1_tarski @ X60)) != (X61)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      (((((sk_B) != (sk_B)) | ~ (r2_hidden @ sk_A @ sk_B)))
% 0.21/0.53         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      ((~ (r2_hidden @ sk_A @ sk_B))
% 0.21/0.53         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.53      inference('simplify', [status(thm)], ['29'])).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) | 
% 0.21/0.53       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['4', '30'])).
% 0.21/0.53  thf('32', plain, (~ ((r2_hidden @ sk_A @ sk_B))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['2', '31'])).
% 0.21/0.53  thf('33', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['1', '32'])).
% 0.21/0.53  thf('34', plain,
% 0.21/0.53      (![X61 : $i, X62 : $i]:
% 0.21/0.53         (((k4_xboole_0 @ X61 @ (k1_tarski @ X62)) = (X61))
% 0.21/0.53          | (r2_hidden @ X62 @ X61))),
% 0.21/0.53      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.21/0.53  thf('35', plain,
% 0.21/0.53      (![X12 : $i, X13 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.21/0.53           = (k3_xboole_0 @ X12 @ X13))),
% 0.21/0.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.53  thf('36', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 0.21/0.53          | (r2_hidden @ X1 @ X0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['34', '35'])).
% 0.21/0.53  thf('37', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.53      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.53  thf('38', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 0.21/0.53          | (r2_hidden @ X1 @ X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['36', '37'])).
% 0.21/0.53  thf('39', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.53  thf('40', plain,
% 0.21/0.53      (![X7 : $i, X8 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ X7 @ X8)
% 0.21/0.53           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.53  thf('41', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ X0 @ X1)
% 0.21/0.53           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['39', '40'])).
% 0.21/0.53  thf('42', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.21/0.53            = (k5_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))
% 0.21/0.53          | (r2_hidden @ X0 @ X1))),
% 0.21/0.53      inference('sup+', [status(thm)], ['38', '41'])).
% 0.21/0.53  thf('43', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.21/0.53      inference('cnf', [status(esa)], [t5_boole])).
% 0.21/0.53  thf('44', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 0.21/0.53          | (r2_hidden @ X0 @ X1))),
% 0.21/0.53      inference('demod', [status(thm)], ['42', '43'])).
% 0.21/0.53  thf('45', plain,
% 0.21/0.53      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A)))
% 0.21/0.53         <= (~
% 0.21/0.53             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.53      inference('split', [status(esa)], ['3'])).
% 0.21/0.53  thf('46', plain,
% 0.21/0.53      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) | 
% 0.21/0.53       ((r2_hidden @ sk_A @ sk_B))),
% 0.21/0.53      inference('split', [status(esa)], ['3'])).
% 0.21/0.53  thf('47', plain,
% 0.21/0.53      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['2', '31', '46'])).
% 0.21/0.53  thf('48', plain,
% 0.21/0.53      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['45', '47'])).
% 0.21/0.53  thf('49', plain,
% 0.21/0.53      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A)) | (r2_hidden @ sk_A @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['44', '48'])).
% 0.21/0.53  thf('50', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.21/0.53      inference('simplify', [status(thm)], ['49'])).
% 0.21/0.53  thf('51', plain, ($false), inference('demod', [status(thm)], ['33', '50'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
