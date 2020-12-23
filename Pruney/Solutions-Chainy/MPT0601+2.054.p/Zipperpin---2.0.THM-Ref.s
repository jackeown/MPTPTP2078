%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WGBBwkuGU5

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:48 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 125 expanded)
%              Number of leaves         :   18 (  43 expanded)
%              Depth                    :   13
%              Number of atoms          :  385 ( 990 expanded)
%              Number of equality atoms :   26 (  66 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('0',plain,(
    ! [X6: $i,X9: $i] :
      ( ( X9
        = ( k1_relat_1 @ X6 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X9 @ X6 ) @ ( sk_D @ X9 @ X6 ) ) @ X6 )
      | ( r2_hidden @ ( sk_C @ X9 @ X6 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X2 ) @ X3 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('6',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('7',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('9',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k11_relat_1 @ X12 @ X13 ) )
      | ( r2_hidden @ ( k4_tarski @ X13 @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_C @ ( k11_relat_1 @ X1 @ X0 ) @ k1_xboole_0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 )
      | ( r2_hidden @ X4 @ X7 )
      | ( X7
       != ( k1_relat_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('12',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k1_relat_1 @ X6 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

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

thf('14',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf('19',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['16'])).

thf('20',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ ( k4_tarski @ X8 @ ( sk_D_1 @ X8 @ X6 ) ) @ X6 )
      | ( X7
       != ( k1_relat_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('21',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X8 @ ( sk_D_1 @ X8 @ X6 ) ) @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_1 @ sk_A @ sk_B ) ) @ sk_B )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X13 @ X11 ) @ X12 )
      | ( r2_hidden @ X11 @ ( k11_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('24',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k11_relat_1 @ sk_B @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k11_relat_1 @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
      & ( ( k11_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['18','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('29',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf('31',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['17','29','30'])).

thf('32',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['15','31'])).

thf('33',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('37',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['17','29'])).

thf('38',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['36','37'])).

thf('39',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['35','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WGBBwkuGU5
% 0.13/0.37  % Computer   : n014.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 11:04:52 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.23/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.51  % Solved by: fo/fo7.sh
% 0.23/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.51  % done 36 iterations in 0.026s
% 0.23/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.51  % SZS output start Refutation
% 0.23/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.23/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.51  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.23/0.51  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.23/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.23/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.51  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.23/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.23/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.51  thf(d4_relat_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.23/0.51       ( ![C:$i]:
% 0.23/0.51         ( ( r2_hidden @ C @ B ) <=>
% 0.23/0.51           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.23/0.51  thf('0', plain,
% 0.23/0.51      (![X6 : $i, X9 : $i]:
% 0.23/0.51         (((X9) = (k1_relat_1 @ X6))
% 0.23/0.51          | (r2_hidden @ (k4_tarski @ (sk_C @ X9 @ X6) @ (sk_D @ X9 @ X6)) @ X6)
% 0.23/0.51          | (r2_hidden @ (sk_C @ X9 @ X6) @ X9))),
% 0.23/0.51      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.23/0.51  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.23/0.51  thf('1', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.23/0.51      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.23/0.51  thf(l24_zfmisc_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.23/0.51  thf('2', plain,
% 0.23/0.51      (![X2 : $i, X3 : $i]:
% 0.23/0.51         (~ (r1_xboole_0 @ (k1_tarski @ X2) @ X3) | ~ (r2_hidden @ X2 @ X3))),
% 0.23/0.51      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.23/0.51  thf('3', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.23/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.51  thf('4', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.23/0.51          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['0', '3'])).
% 0.23/0.51  thf('5', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.23/0.51          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['0', '3'])).
% 0.23/0.51  thf('6', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.23/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.51  thf('7', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.23/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.23/0.51  thf('8', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0) | ((X0) = (k1_xboole_0)))),
% 0.23/0.51      inference('demod', [status(thm)], ['4', '7'])).
% 0.23/0.51  thf(t204_relat_1, axiom,
% 0.23/0.51    (![A:$i,B:$i,C:$i]:
% 0.23/0.51     ( ( v1_relat_1 @ C ) =>
% 0.23/0.51       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.23/0.51         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.23/0.51  thf('9', plain,
% 0.23/0.51      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.23/0.51         (~ (r2_hidden @ X11 @ (k11_relat_1 @ X12 @ X13))
% 0.23/0.51          | (r2_hidden @ (k4_tarski @ X13 @ X11) @ X12)
% 0.23/0.51          | ~ (v1_relat_1 @ X12))),
% 0.23/0.51      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.23/0.51  thf('10', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         (((k11_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.23/0.51          | ~ (v1_relat_1 @ X1)
% 0.23/0.51          | (r2_hidden @ 
% 0.23/0.51             (k4_tarski @ X0 @ (sk_C @ (k11_relat_1 @ X1 @ X0) @ k1_xboole_0)) @ 
% 0.23/0.51             X1))),
% 0.23/0.51      inference('sup-', [status(thm)], ['8', '9'])).
% 0.23/0.51  thf('11', plain,
% 0.23/0.51      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.23/0.51         (~ (r2_hidden @ (k4_tarski @ X4 @ X5) @ X6)
% 0.23/0.51          | (r2_hidden @ X4 @ X7)
% 0.23/0.51          | ((X7) != (k1_relat_1 @ X6)))),
% 0.23/0.51      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.23/0.51  thf('12', plain,
% 0.23/0.51      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.23/0.51         ((r2_hidden @ X4 @ (k1_relat_1 @ X6))
% 0.23/0.51          | ~ (r2_hidden @ (k4_tarski @ X4 @ X5) @ X6))),
% 0.23/0.51      inference('simplify', [status(thm)], ['11'])).
% 0.23/0.51  thf('13', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         (~ (v1_relat_1 @ X0)
% 0.23/0.51          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.23/0.51          | (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['10', '12'])).
% 0.23/0.51  thf(t205_relat_1, conjecture,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( v1_relat_1 @ B ) =>
% 0.23/0.51       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.23/0.51         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.23/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.51    (~( ![A:$i,B:$i]:
% 0.23/0.51        ( ( v1_relat_1 @ B ) =>
% 0.23/0.51          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.23/0.51            ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ) )),
% 0.23/0.51    inference('cnf.neg', [status(esa)], [t205_relat_1])).
% 0.23/0.51  thf('14', plain,
% 0.23/0.51      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))
% 0.23/0.51        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('15', plain,
% 0.23/0.51      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.23/0.51         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.23/0.51      inference('split', [status(esa)], ['14'])).
% 0.23/0.51  thf('16', plain,
% 0.23/0.51      ((((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0))
% 0.23/0.51        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('17', plain,
% 0.23/0.51      (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.23/0.51       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.23/0.51      inference('split', [status(esa)], ['16'])).
% 0.23/0.51  thf('18', plain,
% 0.23/0.51      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.23/0.51         <= ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.23/0.51      inference('split', [status(esa)], ['14'])).
% 0.23/0.51  thf('19', plain,
% 0.23/0.51      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.23/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.23/0.51      inference('split', [status(esa)], ['16'])).
% 0.23/0.51  thf('20', plain,
% 0.23/0.51      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.23/0.51         (~ (r2_hidden @ X8 @ X7)
% 0.23/0.51          | (r2_hidden @ (k4_tarski @ X8 @ (sk_D_1 @ X8 @ X6)) @ X6)
% 0.23/0.51          | ((X7) != (k1_relat_1 @ X6)))),
% 0.23/0.51      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.23/0.51  thf('21', plain,
% 0.23/0.51      (![X6 : $i, X8 : $i]:
% 0.23/0.51         ((r2_hidden @ (k4_tarski @ X8 @ (sk_D_1 @ X8 @ X6)) @ X6)
% 0.23/0.51          | ~ (r2_hidden @ X8 @ (k1_relat_1 @ X6)))),
% 0.23/0.51      inference('simplify', [status(thm)], ['20'])).
% 0.23/0.51  thf('22', plain,
% 0.23/0.51      (((r2_hidden @ (k4_tarski @ sk_A @ (sk_D_1 @ sk_A @ sk_B)) @ sk_B))
% 0.23/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.23/0.51      inference('sup-', [status(thm)], ['19', '21'])).
% 0.23/0.51  thf('23', plain,
% 0.23/0.51      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.23/0.51         (~ (r2_hidden @ (k4_tarski @ X13 @ X11) @ X12)
% 0.23/0.51          | (r2_hidden @ X11 @ (k11_relat_1 @ X12 @ X13))
% 0.23/0.51          | ~ (v1_relat_1 @ X12))),
% 0.23/0.51      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.23/0.51  thf('24', plain,
% 0.23/0.51      (((~ (v1_relat_1 @ sk_B)
% 0.23/0.51         | (r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k11_relat_1 @ sk_B @ sk_A))))
% 0.23/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.23/0.51      inference('sup-', [status(thm)], ['22', '23'])).
% 0.23/0.51  thf('25', plain, ((v1_relat_1 @ sk_B)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('26', plain,
% 0.23/0.51      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k11_relat_1 @ sk_B @ sk_A)))
% 0.23/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.23/0.51      inference('demod', [status(thm)], ['24', '25'])).
% 0.23/0.51  thf('27', plain,
% 0.23/0.51      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ k1_xboole_0))
% 0.23/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) & 
% 0.23/0.51             (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.23/0.51      inference('sup+', [status(thm)], ['18', '26'])).
% 0.23/0.51  thf('28', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.23/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.51  thf('29', plain,
% 0.23/0.51      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) | 
% 0.23/0.51       ~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['27', '28'])).
% 0.23/0.51  thf('30', plain,
% 0.23/0.51      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) | 
% 0.23/0.51       (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.23/0.51      inference('split', [status(esa)], ['14'])).
% 0.23/0.51  thf('31', plain, (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.23/0.51      inference('sat_resolution*', [status(thm)], ['17', '29', '30'])).
% 0.23/0.51  thf('32', plain, (~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.23/0.51      inference('simpl_trail', [status(thm)], ['15', '31'])).
% 0.23/0.51  thf('33', plain,
% 0.23/0.51      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)) | ~ (v1_relat_1 @ sk_B))),
% 0.23/0.51      inference('sup-', [status(thm)], ['13', '32'])).
% 0.23/0.51  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('35', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.23/0.51      inference('demod', [status(thm)], ['33', '34'])).
% 0.23/0.51  thf('36', plain,
% 0.23/0.51      ((((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))
% 0.23/0.51         <= (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.23/0.51      inference('split', [status(esa)], ['16'])).
% 0.23/0.51  thf('37', plain, (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.23/0.51      inference('sat_resolution*', [status(thm)], ['17', '29'])).
% 0.23/0.51  thf('38', plain, (((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0))),
% 0.23/0.51      inference('simpl_trail', [status(thm)], ['36', '37'])).
% 0.23/0.51  thf('39', plain, ($false),
% 0.23/0.51      inference('simplify_reflect-', [status(thm)], ['35', '38'])).
% 0.23/0.51  
% 0.23/0.51  % SZS output end Refutation
% 0.23/0.51  
% 0.23/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
