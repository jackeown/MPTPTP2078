%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NSD1W97vrO

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:11 EST 2020

% Result     : Theorem 0.79s
% Output     : Refutation 0.79s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 237 expanded)
%              Number of leaves         :   16 (  61 expanded)
%              Depth                    :   22
%              Number of atoms          :  541 (1959 expanded)
%              Number of equality atoms :   64 ( 284 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

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
      = ( k1_tarski @ sk_B_1 ) )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) )
   <= ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B_1 ) )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('6',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('7',plain,(
    ! [X12: $i] :
      ( r1_tarski @ k1_xboole_0 @ X12 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('8',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('9',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('10',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
   <= ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['6','11'])).

thf('13',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['5','12'])).

thf('14',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B_1 ) )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['4','13'])).

thf('15',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('16',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference(demod,[status(thm)],['3','16','18'])).

thf('20',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['19'])).

thf('21',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','20'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('22',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('23',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    = sk_A ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('24',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('25',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    = sk_A ),
    inference('sup-',[status(thm)],['21','22'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('26',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('27',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_A ) @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['24','28'])).

thf('30',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['5','12'])).

thf('31',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ ( k1_tarski @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('32',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ( X16 = X13 )
      | ( X15
       != ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('33',plain,(
    ! [X13: $i,X16: $i] :
      ( ( X16 = X13 )
      | ~ ( r2_hidden @ X16 @ ( k1_tarski @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( sk_B @ sk_A )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('36',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['5','12'])).

thf('38',plain,(
    r2_hidden @ sk_B_1 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['39'])).

thf('41',plain,(
    ! [X13: $i,X16: $i] :
      ( ( X16 = X13 )
      | ~ ( r2_hidden @ X16 @ ( k1_tarski @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['39'])).

thf('44',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['39'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['42','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( k1_tarski @ sk_B_1 )
    = ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['38','50'])).

thf('52',plain,
    ( ( k1_tarski @ sk_B_1 )
    = sk_A ),
    inference('sup+',[status(thm)],['23','51'])).

thf('53',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B_1 ) )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B_1 ) )
   <= ( sk_A
     != ( k1_tarski @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['53'])).

thf('55',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B_1 ) )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['53'])).

thf('56',plain,(
    sk_A
 != ( k1_tarski @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['19','55'])).

thf('57',plain,(
    sk_A
 != ( k1_tarski @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['54','56'])).

thf('58',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['52','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NSD1W97vrO
% 0.14/0.36  % Computer   : n012.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 10:17:52 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.79/0.97  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.79/0.97  % Solved by: fo/fo7.sh
% 0.79/0.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.79/0.97  % done 779 iterations in 0.498s
% 0.79/0.97  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.79/0.97  % SZS output start Refutation
% 0.79/0.97  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.79/0.97  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.79/0.97  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.79/0.97  thf(sk_A_type, type, sk_A: $i).
% 0.79/0.97  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.79/0.97  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.79/0.97  thf(sk_B_type, type, sk_B: $i > $i).
% 0.79/0.97  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.79/0.97  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.79/0.97  thf(t39_zfmisc_1, conjecture,
% 0.79/0.97    (![A:$i,B:$i]:
% 0.79/0.97     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.79/0.97       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.79/0.97  thf(zf_stmt_0, negated_conjecture,
% 0.79/0.97    (~( ![A:$i,B:$i]:
% 0.79/0.97        ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.79/0.97          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ) )),
% 0.79/0.97    inference('cnf.neg', [status(esa)], [t39_zfmisc_1])).
% 0.79/0.97  thf('0', plain,
% 0.79/0.97      ((((sk_A) = (k1_tarski @ sk_B_1))
% 0.79/0.97        | ((sk_A) = (k1_xboole_0))
% 0.79/0.97        | (r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('1', plain,
% 0.79/0.97      (((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.79/0.97         <= (((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.79/0.97      inference('split', [status(esa)], ['0'])).
% 0.79/0.97  thf('2', plain,
% 0.79/0.97      ((((sk_A) != (k1_xboole_0)) | ~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('3', plain,
% 0.79/0.97      ((~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.79/0.97         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.79/0.97      inference('split', [status(esa)], ['2'])).
% 0.79/0.97  thf('4', plain,
% 0.79/0.97      ((((sk_A) = (k1_tarski @ sk_B_1))
% 0.79/0.97        | ((sk_A) = (k1_xboole_0))
% 0.79/0.97        | (r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('5', plain,
% 0.79/0.97      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.79/0.97      inference('split', [status(esa)], ['2'])).
% 0.79/0.97  thf('6', plain,
% 0.79/0.97      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.79/0.97       ~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.79/0.97      inference('split', [status(esa)], ['2'])).
% 0.79/0.97  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.79/0.97  thf('7', plain, (![X12 : $i]: (r1_tarski @ k1_xboole_0 @ X12)),
% 0.79/0.97      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.79/0.97  thf('8', plain, ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.79/0.97      inference('split', [status(esa)], ['0'])).
% 0.79/0.97  thf('9', plain,
% 0.79/0.97      ((~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.79/0.97         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.79/0.97      inference('split', [status(esa)], ['2'])).
% 0.79/0.97  thf('10', plain,
% 0.79/0.97      ((~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ sk_B_1)))
% 0.79/0.97         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))) & 
% 0.79/0.97             (((sk_A) = (k1_xboole_0))))),
% 0.79/0.97      inference('sup-', [status(thm)], ['8', '9'])).
% 0.79/0.97  thf('11', plain,
% 0.79/0.97      (((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))) | 
% 0.79/0.97       ~ (((sk_A) = (k1_xboole_0)))),
% 0.79/0.97      inference('sup-', [status(thm)], ['7', '10'])).
% 0.79/0.97  thf('12', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.79/0.97      inference('sat_resolution*', [status(thm)], ['6', '11'])).
% 0.79/0.97  thf('13', plain, (((sk_A) != (k1_xboole_0))),
% 0.79/0.97      inference('simpl_trail', [status(thm)], ['5', '12'])).
% 0.79/0.97  thf('14', plain,
% 0.79/0.97      ((((sk_A) = (k1_tarski @ sk_B_1))
% 0.79/0.97        | (r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.79/0.97      inference('simplify_reflect-', [status(thm)], ['4', '13'])).
% 0.79/0.97  thf('15', plain,
% 0.79/0.97      ((~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.79/0.97         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.79/0.97      inference('split', [status(esa)], ['2'])).
% 0.79/0.97  thf('16', plain,
% 0.79/0.97      ((((sk_A) = (k1_tarski @ sk_B_1)))
% 0.79/0.97         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.79/0.97      inference('sup-', [status(thm)], ['14', '15'])).
% 0.79/0.97  thf(d10_xboole_0, axiom,
% 0.79/0.97    (![A:$i,B:$i]:
% 0.79/0.97     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.79/0.97  thf('17', plain,
% 0.79/0.97      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 0.79/0.97      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.79/0.97  thf('18', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 0.79/0.97      inference('simplify', [status(thm)], ['17'])).
% 0.79/0.97  thf('19', plain, (((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.79/0.97      inference('demod', [status(thm)], ['3', '16', '18'])).
% 0.79/0.97  thf('20', plain, (((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.79/0.97      inference('sat_resolution*', [status(thm)], ['19'])).
% 0.79/0.97  thf('21', plain, ((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.79/0.97      inference('simpl_trail', [status(thm)], ['1', '20'])).
% 0.79/0.97  thf(t28_xboole_1, axiom,
% 0.79/0.97    (![A:$i,B:$i]:
% 0.79/0.97     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.79/0.97  thf('22', plain,
% 0.79/0.97      (![X10 : $i, X11 : $i]:
% 0.79/0.97         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.79/0.97      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.79/0.97  thf('23', plain, (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))),
% 0.79/0.97      inference('sup-', [status(thm)], ['21', '22'])).
% 0.79/0.97  thf(t7_xboole_0, axiom,
% 0.79/0.97    (![A:$i]:
% 0.79/0.97     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.79/0.97          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.79/0.97  thf('24', plain,
% 0.79/0.97      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.79/0.97      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.79/0.97  thf('25', plain, (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))),
% 0.79/0.97      inference('sup-', [status(thm)], ['21', '22'])).
% 0.79/0.97  thf(d4_xboole_0, axiom,
% 0.79/0.97    (![A:$i,B:$i,C:$i]:
% 0.79/0.97     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.79/0.97       ( ![D:$i]:
% 0.79/0.97         ( ( r2_hidden @ D @ C ) <=>
% 0.79/0.97           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.79/0.97  thf('26', plain,
% 0.79/0.97      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.79/0.97         (~ (r2_hidden @ X4 @ X3)
% 0.79/0.97          | (r2_hidden @ X4 @ X2)
% 0.79/0.97          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.79/0.97      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.79/0.97  thf('27', plain,
% 0.79/0.97      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.79/0.97         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.79/0.97      inference('simplify', [status(thm)], ['26'])).
% 0.79/0.97  thf('28', plain,
% 0.79/0.97      (![X0 : $i]:
% 0.79/0.97         (~ (r2_hidden @ X0 @ sk_A) | (r2_hidden @ X0 @ (k1_tarski @ sk_B_1)))),
% 0.79/0.97      inference('sup-', [status(thm)], ['25', '27'])).
% 0.79/0.97  thf('29', plain,
% 0.79/0.97      ((((sk_A) = (k1_xboole_0))
% 0.79/0.97        | (r2_hidden @ (sk_B @ sk_A) @ (k1_tarski @ sk_B_1)))),
% 0.79/0.97      inference('sup-', [status(thm)], ['24', '28'])).
% 0.79/0.97  thf('30', plain, (((sk_A) != (k1_xboole_0))),
% 0.79/0.97      inference('simpl_trail', [status(thm)], ['5', '12'])).
% 0.79/0.97  thf('31', plain, ((r2_hidden @ (sk_B @ sk_A) @ (k1_tarski @ sk_B_1))),
% 0.79/0.97      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.79/0.97  thf(d1_tarski, axiom,
% 0.79/0.97    (![A:$i,B:$i]:
% 0.79/0.97     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.79/0.97       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.79/0.97  thf('32', plain,
% 0.79/0.97      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.79/0.97         (~ (r2_hidden @ X16 @ X15)
% 0.79/0.97          | ((X16) = (X13))
% 0.79/0.97          | ((X15) != (k1_tarski @ X13)))),
% 0.79/0.97      inference('cnf', [status(esa)], [d1_tarski])).
% 0.79/0.97  thf('33', plain,
% 0.79/0.97      (![X13 : $i, X16 : $i]:
% 0.79/0.97         (((X16) = (X13)) | ~ (r2_hidden @ X16 @ (k1_tarski @ X13)))),
% 0.79/0.97      inference('simplify', [status(thm)], ['32'])).
% 0.79/0.97  thf('34', plain, (((sk_B @ sk_A) = (sk_B_1))),
% 0.79/0.97      inference('sup-', [status(thm)], ['31', '33'])).
% 0.79/0.97  thf('35', plain,
% 0.79/0.97      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.79/0.97      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.79/0.97  thf('36', plain, (((r2_hidden @ sk_B_1 @ sk_A) | ((sk_A) = (k1_xboole_0)))),
% 0.79/0.97      inference('sup+', [status(thm)], ['34', '35'])).
% 0.79/0.97  thf('37', plain, (((sk_A) != (k1_xboole_0))),
% 0.79/0.97      inference('simpl_trail', [status(thm)], ['5', '12'])).
% 0.79/0.97  thf('38', plain, ((r2_hidden @ sk_B_1 @ sk_A)),
% 0.79/0.97      inference('simplify_reflect-', [status(thm)], ['36', '37'])).
% 0.79/0.97  thf('39', plain,
% 0.79/0.97      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.79/0.97         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.79/0.97          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.79/0.97          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.79/0.97      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.79/0.97  thf('40', plain,
% 0.79/0.97      (![X0 : $i, X1 : $i]:
% 0.79/0.97         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.79/0.97          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.79/0.97      inference('eq_fact', [status(thm)], ['39'])).
% 0.79/0.97  thf('41', plain,
% 0.79/0.97      (![X13 : $i, X16 : $i]:
% 0.79/0.97         (((X16) = (X13)) | ~ (r2_hidden @ X16 @ (k1_tarski @ X13)))),
% 0.79/0.97      inference('simplify', [status(thm)], ['32'])).
% 0.79/0.97  thf('42', plain,
% 0.79/0.97      (![X0 : $i, X1 : $i]:
% 0.79/0.97         (((k1_tarski @ X0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.79/0.97          | ((sk_D @ (k1_tarski @ X0) @ (k1_tarski @ X0) @ X1) = (X0)))),
% 0.79/0.97      inference('sup-', [status(thm)], ['40', '41'])).
% 0.79/0.97  thf('43', plain,
% 0.79/0.97      (![X0 : $i, X1 : $i]:
% 0.79/0.97         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.79/0.97          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.79/0.97      inference('eq_fact', [status(thm)], ['39'])).
% 0.79/0.97  thf('44', plain,
% 0.79/0.97      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.79/0.97         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.79/0.97          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.79/0.97          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.79/0.97          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.79/0.97      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.79/0.97  thf('45', plain,
% 0.79/0.97      (![X0 : $i, X1 : $i]:
% 0.79/0.97         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 0.79/0.97          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.79/0.97          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.79/0.97          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.79/0.97      inference('sup-', [status(thm)], ['43', '44'])).
% 0.79/0.97  thf('46', plain,
% 0.79/0.97      (![X0 : $i, X1 : $i]:
% 0.79/0.97         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.79/0.97          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.79/0.97          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.79/0.97      inference('simplify', [status(thm)], ['45'])).
% 0.79/0.97  thf('47', plain,
% 0.79/0.97      (![X0 : $i, X1 : $i]:
% 0.79/0.97         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.79/0.97          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.79/0.97      inference('eq_fact', [status(thm)], ['39'])).
% 0.79/0.97  thf('48', plain,
% 0.79/0.97      (![X0 : $i, X1 : $i]:
% 0.79/0.97         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 0.79/0.97          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 0.79/0.97      inference('clc', [status(thm)], ['46', '47'])).
% 0.79/0.97  thf('49', plain,
% 0.79/0.97      (![X0 : $i, X1 : $i]:
% 0.79/0.97         (~ (r2_hidden @ X0 @ X1)
% 0.79/0.97          | ((k1_tarski @ X0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.79/0.97          | ((k1_tarski @ X0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 0.79/0.97      inference('sup-', [status(thm)], ['42', '48'])).
% 0.79/0.97  thf('50', plain,
% 0.79/0.97      (![X0 : $i, X1 : $i]:
% 0.79/0.97         (((k1_tarski @ X0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.79/0.97          | ~ (r2_hidden @ X0 @ X1))),
% 0.79/0.97      inference('simplify', [status(thm)], ['49'])).
% 0.79/0.97  thf('51', plain,
% 0.79/0.97      (((k1_tarski @ sk_B_1) = (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.79/0.97      inference('sup-', [status(thm)], ['38', '50'])).
% 0.79/0.97  thf('52', plain, (((k1_tarski @ sk_B_1) = (sk_A))),
% 0.79/0.97      inference('sup+', [status(thm)], ['23', '51'])).
% 0.79/0.97  thf('53', plain,
% 0.79/0.97      ((((sk_A) != (k1_tarski @ sk_B_1))
% 0.79/0.97        | ~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.79/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.97  thf('54', plain,
% 0.79/0.97      ((((sk_A) != (k1_tarski @ sk_B_1)))
% 0.79/0.97         <= (~ (((sk_A) = (k1_tarski @ sk_B_1))))),
% 0.79/0.97      inference('split', [status(esa)], ['53'])).
% 0.79/0.97  thf('55', plain,
% 0.79/0.97      (~ (((sk_A) = (k1_tarski @ sk_B_1))) | 
% 0.79/0.97       ~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.79/0.97      inference('split', [status(esa)], ['53'])).
% 0.79/0.97  thf('56', plain, (~ (((sk_A) = (k1_tarski @ sk_B_1)))),
% 0.79/0.97      inference('sat_resolution*', [status(thm)], ['19', '55'])).
% 0.79/0.97  thf('57', plain, (((sk_A) != (k1_tarski @ sk_B_1))),
% 0.79/0.97      inference('simpl_trail', [status(thm)], ['54', '56'])).
% 0.79/0.97  thf('58', plain, ($false),
% 0.79/0.97      inference('simplify_reflect-', [status(thm)], ['52', '57'])).
% 0.79/0.97  
% 0.79/0.97  % SZS output end Refutation
% 0.79/0.97  
% 0.79/0.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
