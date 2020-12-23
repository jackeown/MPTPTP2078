%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YX6rtq9Mvw

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:48 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 109 expanded)
%              Number of leaves         :   18 (  37 expanded)
%              Depth                    :   13
%              Number of atoms          :  364 ( 884 expanded)
%              Number of equality atoms :   24 (  61 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( r1_xboole_0 @ X2 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X3 ) @ X4 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k11_relat_1 @ X13 @ X14 ) )
      | ( r2_hidden @ ( k4_tarski @ X14 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_C @ k1_xboole_0 @ ( k11_relat_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X5 @ X6 ) @ X7 )
      | ( r2_hidden @ X5 @ X8 )
      | ( X8
       != ( k1_relat_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('8',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X5 @ ( k1_relat_1 @ X7 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X6 ) @ X7 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf(t205_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
        <=> ( ( k11_relat_1 @ B @ A )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t205_relat_1])).

thf('10',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('15',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['12'])).

thf('16',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X8 )
      | ( r2_hidden @ ( k4_tarski @ X9 @ ( sk_D_1 @ X9 @ X7 ) ) @ X7 )
      | ( X8
       != ( k1_relat_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('17',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X9 @ ( sk_D_1 @ X9 @ X7 ) ) @ X7 )
      | ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_1 @ sk_A @ sk_B ) ) @ sk_B )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X14 @ X12 ) @ X13 )
      | ( r2_hidden @ X12 @ ( k11_relat_1 @ X13 @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('20',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k11_relat_1 @ sk_B @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k11_relat_1 @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
      & ( ( k11_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('25',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('27',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['13','25','26'])).

thf('28',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['11','27'])).

thf('29',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['9','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('33',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['13','25'])).

thf('34',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['32','33'])).

thf('35',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['31','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YX6rtq9Mvw
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:58:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.19/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.51  % Solved by: fo/fo7.sh
% 0.19/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.51  % done 54 iterations in 0.056s
% 0.19/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.51  % SZS output start Refutation
% 0.19/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.51  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.19/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.51  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.19/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.51  thf(t2_tarski, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.19/0.51       ( ( A ) = ( B ) ) ))).
% 0.19/0.51  thf('0', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (((X1) = (X0))
% 0.19/0.51          | (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.19/0.51          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.19/0.51      inference('cnf', [status(esa)], [t2_tarski])).
% 0.19/0.51  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.19/0.51  thf('1', plain, (![X2 : $i]: (r1_xboole_0 @ X2 @ k1_xboole_0)),
% 0.19/0.51      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.19/0.51  thf(l24_zfmisc_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.19/0.51  thf('2', plain,
% 0.19/0.51      (![X3 : $i, X4 : $i]:
% 0.19/0.51         (~ (r1_xboole_0 @ (k1_tarski @ X3) @ X4) | ~ (r2_hidden @ X3 @ X4))),
% 0.19/0.51      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.19/0.51  thf('3', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.19/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.51  thf('4', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ X0) | ((X0) = (k1_xboole_0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['0', '3'])).
% 0.19/0.51  thf(t204_relat_1, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i]:
% 0.19/0.51     ( ( v1_relat_1 @ C ) =>
% 0.19/0.51       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.19/0.51         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.19/0.51  thf('5', plain,
% 0.19/0.51      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.51         (~ (r2_hidden @ X12 @ (k11_relat_1 @ X13 @ X14))
% 0.19/0.51          | (r2_hidden @ (k4_tarski @ X14 @ X12) @ X13)
% 0.19/0.51          | ~ (v1_relat_1 @ X13))),
% 0.19/0.51      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.19/0.51  thf('6', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (((k11_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.19/0.51          | ~ (v1_relat_1 @ X1)
% 0.19/0.51          | (r2_hidden @ 
% 0.19/0.51             (k4_tarski @ X0 @ (sk_C @ k1_xboole_0 @ (k11_relat_1 @ X1 @ X0))) @ 
% 0.19/0.51             X1))),
% 0.19/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.51  thf(d4_relat_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.19/0.51       ( ![C:$i]:
% 0.19/0.51         ( ( r2_hidden @ C @ B ) <=>
% 0.19/0.51           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.19/0.51  thf('7', plain,
% 0.19/0.51      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.51         (~ (r2_hidden @ (k4_tarski @ X5 @ X6) @ X7)
% 0.19/0.51          | (r2_hidden @ X5 @ X8)
% 0.19/0.51          | ((X8) != (k1_relat_1 @ X7)))),
% 0.19/0.51      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.19/0.51  thf('8', plain,
% 0.19/0.51      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.19/0.51         ((r2_hidden @ X5 @ (k1_relat_1 @ X7))
% 0.19/0.51          | ~ (r2_hidden @ (k4_tarski @ X5 @ X6) @ X7))),
% 0.19/0.51      inference('simplify', [status(thm)], ['7'])).
% 0.19/0.51  thf('9', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (~ (v1_relat_1 @ X0)
% 0.19/0.51          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.19/0.51          | (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['6', '8'])).
% 0.19/0.51  thf(t205_relat_1, conjecture,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( v1_relat_1 @ B ) =>
% 0.19/0.51       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.19/0.51         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.19/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.51    (~( ![A:$i,B:$i]:
% 0.19/0.51        ( ( v1_relat_1 @ B ) =>
% 0.19/0.51          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.19/0.51            ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ) )),
% 0.19/0.51    inference('cnf.neg', [status(esa)], [t205_relat_1])).
% 0.19/0.51  thf('10', plain,
% 0.19/0.51      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))
% 0.19/0.51        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('11', plain,
% 0.19/0.51      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.19/0.51         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.19/0.51      inference('split', [status(esa)], ['10'])).
% 0.19/0.51  thf('12', plain,
% 0.19/0.51      ((((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0))
% 0.19/0.51        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('13', plain,
% 0.19/0.51      (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.19/0.51       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.19/0.51      inference('split', [status(esa)], ['12'])).
% 0.19/0.51  thf('14', plain,
% 0.19/0.51      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.19/0.51         <= ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.19/0.51      inference('split', [status(esa)], ['10'])).
% 0.19/0.51  thf('15', plain,
% 0.19/0.51      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.19/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.19/0.51      inference('split', [status(esa)], ['12'])).
% 0.19/0.51  thf('16', plain,
% 0.19/0.51      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.51         (~ (r2_hidden @ X9 @ X8)
% 0.19/0.51          | (r2_hidden @ (k4_tarski @ X9 @ (sk_D_1 @ X9 @ X7)) @ X7)
% 0.19/0.51          | ((X8) != (k1_relat_1 @ X7)))),
% 0.19/0.51      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.19/0.51  thf('17', plain,
% 0.19/0.51      (![X7 : $i, X9 : $i]:
% 0.19/0.51         ((r2_hidden @ (k4_tarski @ X9 @ (sk_D_1 @ X9 @ X7)) @ X7)
% 0.19/0.51          | ~ (r2_hidden @ X9 @ (k1_relat_1 @ X7)))),
% 0.19/0.51      inference('simplify', [status(thm)], ['16'])).
% 0.19/0.51  thf('18', plain,
% 0.19/0.51      (((r2_hidden @ (k4_tarski @ sk_A @ (sk_D_1 @ sk_A @ sk_B)) @ sk_B))
% 0.19/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.19/0.51      inference('sup-', [status(thm)], ['15', '17'])).
% 0.19/0.51  thf('19', plain,
% 0.19/0.51      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.51         (~ (r2_hidden @ (k4_tarski @ X14 @ X12) @ X13)
% 0.19/0.51          | (r2_hidden @ X12 @ (k11_relat_1 @ X13 @ X14))
% 0.19/0.51          | ~ (v1_relat_1 @ X13))),
% 0.19/0.51      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.19/0.51  thf('20', plain,
% 0.19/0.51      (((~ (v1_relat_1 @ sk_B)
% 0.19/0.51         | (r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k11_relat_1 @ sk_B @ sk_A))))
% 0.19/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.19/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.51  thf('21', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('22', plain,
% 0.19/0.51      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k11_relat_1 @ sk_B @ sk_A)))
% 0.19/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.19/0.51      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.51  thf('23', plain,
% 0.19/0.51      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ k1_xboole_0))
% 0.19/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) & 
% 0.19/0.51             (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.19/0.51      inference('sup+', [status(thm)], ['14', '22'])).
% 0.19/0.51  thf('24', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.19/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.51  thf('25', plain,
% 0.19/0.51      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) | 
% 0.19/0.51       ~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.19/0.51  thf('26', plain,
% 0.19/0.51      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) | 
% 0.19/0.51       (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.19/0.51      inference('split', [status(esa)], ['10'])).
% 0.19/0.51  thf('27', plain, (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.19/0.51      inference('sat_resolution*', [status(thm)], ['13', '25', '26'])).
% 0.19/0.51  thf('28', plain, (~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.19/0.51      inference('simpl_trail', [status(thm)], ['11', '27'])).
% 0.19/0.51  thf('29', plain,
% 0.19/0.51      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)) | ~ (v1_relat_1 @ sk_B))),
% 0.19/0.51      inference('sup-', [status(thm)], ['9', '28'])).
% 0.19/0.51  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('31', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.19/0.51      inference('demod', [status(thm)], ['29', '30'])).
% 0.19/0.51  thf('32', plain,
% 0.19/0.51      ((((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))
% 0.19/0.51         <= (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.19/0.51      inference('split', [status(esa)], ['12'])).
% 0.19/0.51  thf('33', plain, (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.19/0.51      inference('sat_resolution*', [status(thm)], ['13', '25'])).
% 0.19/0.51  thf('34', plain, (((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0))),
% 0.19/0.51      inference('simpl_trail', [status(thm)], ['32', '33'])).
% 0.19/0.51  thf('35', plain, ($false),
% 0.19/0.51      inference('simplify_reflect-', [status(thm)], ['31', '34'])).
% 0.19/0.51  
% 0.19/0.51  % SZS output end Refutation
% 0.19/0.51  
% 0.19/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
