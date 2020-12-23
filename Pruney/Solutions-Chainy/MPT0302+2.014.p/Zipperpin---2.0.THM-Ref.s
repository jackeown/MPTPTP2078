%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3tMBtGUw0q

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:07 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   59 (  83 expanded)
%              Number of leaves         :   19 (  33 expanded)
%              Depth                    :   13
%              Number of atoms          :  410 ( 675 expanded)
%              Number of equality atoms :   27 (  63 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5 = X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X13: $i] :
      ( ( k3_xboole_0 @ X13 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X6 @ X9 ) )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('5',plain,(
    ! [X14: $i] :
      ( r1_xboole_0 @ X14 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('6',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('8',plain,(
    ! [X15: $i,X16: $i,X17: $i,X19: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ ( k2_zfmisc_1 @ X16 @ X19 ) )
      | ~ ( r2_hidden @ X17 @ X19 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_C_1 @ X0 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_C_1 @ X2 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( k1_xboole_0 = X2 ) ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf(t114_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = ( k2_zfmisc_1 @ B @ A ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( A = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_zfmisc_1 @ A @ B )
          = ( k2_zfmisc_1 @ B @ A ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( A = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t114_zfmisc_1])).

thf('11',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ~ ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ ( k2_zfmisc_1 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = sk_B )
      | ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['18'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('25',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,(
    ! [X15: $i,X16: $i,X17: $i,X19: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ ( k2_zfmisc_1 @ X16 @ X19 ) )
      | ~ ( r2_hidden @ X17 @ X19 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ ( sk_C @ X2 @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r1_tarski @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X17 @ X18 )
      | ~ ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ ( k2_zfmisc_1 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( k1_xboole_0 = sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('36',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    $false ),
    inference(demod,[status(thm)],['23','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3tMBtGUw0q
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 16:58:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 102 iterations in 0.057s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.52  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.22/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.52  thf(d3_tarski, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.52  thf('0', plain,
% 0.22/0.52      (![X1 : $i, X3 : $i]:
% 0.22/0.52         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.22/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.52  thf(t2_tarski, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.22/0.52       ( ( A ) = ( B ) ) ))).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      (![X4 : $i, X5 : $i]:
% 0.22/0.52         (((X5) = (X4))
% 0.22/0.52          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X4)
% 0.22/0.52          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X5))),
% 0.22/0.52      inference('cnf', [status(esa)], [t2_tarski])).
% 0.22/0.52  thf(t2_boole, axiom,
% 0.22/0.52    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.52  thf('2', plain,
% 0.22/0.52      (![X13 : $i]: ((k3_xboole_0 @ X13 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.52      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.52  thf(t4_xboole_0, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.52            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.52       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.22/0.52            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.22/0.52  thf('3', plain,
% 0.22/0.52      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X8 @ (k3_xboole_0 @ X6 @ X9))
% 0.22/0.52          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.22/0.52      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.52  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.22/0.52  thf('5', plain, (![X14 : $i]: (r1_xboole_0 @ X14 @ k1_xboole_0)),
% 0.22/0.52      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.22/0.52  thf('6', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.22/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.22/0.52  thf('7', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.22/0.52          | ((k1_xboole_0) = (X0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['1', '6'])).
% 0.22/0.52  thf(l54_zfmisc_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.52     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.22/0.52       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      (![X15 : $i, X16 : $i, X17 : $i, X19 : $i]:
% 0.22/0.52         ((r2_hidden @ (k4_tarski @ X15 @ X17) @ (k2_zfmisc_1 @ X16 @ X19))
% 0.22/0.52          | ~ (r2_hidden @ X17 @ X19)
% 0.22/0.52          | ~ (r2_hidden @ X15 @ X16))),
% 0.22/0.52      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.22/0.52  thf('9', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.52         (((k1_xboole_0) = (X0))
% 0.22/0.52          | ~ (r2_hidden @ X2 @ X1)
% 0.22/0.52          | (r2_hidden @ (k4_tarski @ X2 @ (sk_C_1 @ X0 @ k1_xboole_0)) @ 
% 0.22/0.52             (k2_zfmisc_1 @ X1 @ X0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.52  thf('10', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.52         ((r1_tarski @ X0 @ X1)
% 0.22/0.52          | (r2_hidden @ 
% 0.22/0.52             (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_C_1 @ X2 @ k1_xboole_0)) @ 
% 0.22/0.52             (k2_zfmisc_1 @ X0 @ X2))
% 0.22/0.52          | ((k1_xboole_0) = (X2)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['0', '9'])).
% 0.22/0.52  thf(t114_zfmisc_1, conjecture,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 0.22/0.52       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.22/0.52         ( ( A ) = ( B ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i,B:$i]:
% 0.22/0.52        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 0.22/0.52          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.22/0.52            ( ( A ) = ( B ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t114_zfmisc_1])).
% 0.22/0.52  thf('11', plain,
% 0.22/0.52      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_B @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('12', plain,
% 0.22/0.52      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.52         ((r2_hidden @ X15 @ X16)
% 0.22/0.52          | ~ (r2_hidden @ (k4_tarski @ X15 @ X17) @ (k2_zfmisc_1 @ X16 @ X18)))),
% 0.22/0.52      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.22/0.52          | (r2_hidden @ X1 @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.52  thf('14', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k1_xboole_0) = (sk_B))
% 0.22/0.52          | (r1_tarski @ sk_A @ X0)
% 0.22/0.52          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['10', '13'])).
% 0.22/0.52  thf('15', plain, (((sk_B) != (k1_xboole_0))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((r1_tarski @ sk_A @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.22/0.52  thf('17', plain,
% 0.22/0.52      (![X1 : $i, X3 : $i]:
% 0.22/0.52         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.22/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.52  thf('18', plain, (((r1_tarski @ sk_A @ sk_B) | (r1_tarski @ sk_A @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.52  thf('19', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.22/0.52      inference('simplify', [status(thm)], ['18'])).
% 0.22/0.52  thf(d10_xboole_0, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.52  thf('20', plain,
% 0.22/0.52      (![X10 : $i, X12 : $i]:
% 0.22/0.52         (((X10) = (X12))
% 0.22/0.52          | ~ (r1_tarski @ X12 @ X10)
% 0.22/0.52          | ~ (r1_tarski @ X10 @ X12))),
% 0.22/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.52  thf('21', plain, ((~ (r1_tarski @ sk_B @ sk_A) | ((sk_B) = (sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.52  thf('22', plain, (((sk_A) != (sk_B))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('23', plain, (~ (r1_tarski @ sk_B @ sk_A)),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.22/0.52          | ((k1_xboole_0) = (X0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['1', '6'])).
% 0.22/0.52  thf('25', plain,
% 0.22/0.52      (![X1 : $i, X3 : $i]:
% 0.22/0.52         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.22/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.52  thf('26', plain,
% 0.22/0.52      (![X15 : $i, X16 : $i, X17 : $i, X19 : $i]:
% 0.22/0.52         ((r2_hidden @ (k4_tarski @ X15 @ X17) @ (k2_zfmisc_1 @ X16 @ X19))
% 0.22/0.52          | ~ (r2_hidden @ X17 @ X19)
% 0.22/0.52          | ~ (r2_hidden @ X15 @ X16))),
% 0.22/0.52      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.22/0.52  thf('27', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.52         ((r1_tarski @ X0 @ X1)
% 0.22/0.52          | ~ (r2_hidden @ X3 @ X2)
% 0.22/0.52          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 0.22/0.52             (k2_zfmisc_1 @ X2 @ X0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.52  thf('28', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.52         (((k1_xboole_0) = (X0))
% 0.22/0.52          | (r2_hidden @ 
% 0.22/0.52             (k4_tarski @ (sk_C_1 @ X0 @ k1_xboole_0) @ (sk_C @ X2 @ X1)) @ 
% 0.22/0.52             (k2_zfmisc_1 @ X0 @ X1))
% 0.22/0.52          | (r1_tarski @ X1 @ X2))),
% 0.22/0.52      inference('sup-', [status(thm)], ['24', '27'])).
% 0.22/0.52  thf('29', plain,
% 0.22/0.52      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_B @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('30', plain,
% 0.22/0.52      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.52         ((r2_hidden @ X17 @ X18)
% 0.22/0.52          | ~ (r2_hidden @ (k4_tarski @ X15 @ X17) @ (k2_zfmisc_1 @ X16 @ X18)))),
% 0.22/0.52      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.22/0.52  thf('31', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.22/0.52          | (r2_hidden @ X0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.52  thf('32', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((r1_tarski @ sk_B @ X0)
% 0.22/0.52          | ((k1_xboole_0) = (sk_A))
% 0.22/0.52          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['28', '31'])).
% 0.22/0.52  thf('33', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('34', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((r1_tarski @ sk_B @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['32', '33'])).
% 0.22/0.52  thf('35', plain,
% 0.22/0.52      (![X1 : $i, X3 : $i]:
% 0.22/0.52         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.22/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.52  thf('36', plain, (((r1_tarski @ sk_B @ sk_A) | (r1_tarski @ sk_B @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['34', '35'])).
% 0.22/0.52  thf('37', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.22/0.52      inference('simplify', [status(thm)], ['36'])).
% 0.22/0.52  thf('38', plain, ($false), inference('demod', [status(thm)], ['23', '37'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
