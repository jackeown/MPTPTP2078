%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BCF58ix9jA

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:24 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :   55 (  79 expanded)
%              Number of leaves         :   19 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :  336 ( 559 expanded)
%              Number of equality atoms :   29 (  63 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t130_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( A != k1_xboole_0 )
     => ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A )
         != k1_xboole_0 )
        & ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( A != k1_xboole_0 )
       => ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A )
           != k1_xboole_0 )
          & ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t130_zfmisc_1])).

thf('1',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( sk_A != X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('7',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t128_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) )
    <=> ( ( A = C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('8',plain,(
    ! [X38: $i,X39: $i,X40: $i,X42: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X39 @ X40 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X38 ) @ X42 ) )
      | ~ ( r2_hidden @ X40 @ X42 )
      | ( X39 != X38 ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('9',plain,(
    ! [X38: $i,X40: $i,X42: $i] :
      ( ~ ( r2_hidden @ X40 @ X42 )
      | ( r2_hidden @ ( k4_tarski @ X38 @ X40 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X38 ) @ X42 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_B @ X0 ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ sk_B_1 @ ( sk_B @ sk_A ) ) @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['6','10'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('12',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
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

thf('13',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('15',plain,(
    ! [X9: $i] :
      ( r1_xboole_0 @ X9 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('16',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( v1_xboole_0 @ sk_A )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['11','16'])).

thf('18',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['2'])).

thf('19',plain,(
    ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('21',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['5','21'])).

thf('23',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t129_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( B = D ) ) ) )).

thf('24',plain,(
    ! [X43: $i,X44: $i,X45: $i,X47: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X43 @ X45 ) @ ( k2_zfmisc_1 @ X44 @ ( k1_tarski @ X47 ) ) )
      | ( X45 != X47 )
      | ~ ( r2_hidden @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('25',plain,(
    ! [X43: $i,X44: $i,X47: $i] :
      ( ~ ( r2_hidden @ X43 @ X44 )
      | ( r2_hidden @ ( k4_tarski @ X43 @ X47 ) @ ( k2_zfmisc_1 @ X44 @ ( k1_tarski @ X47 ) ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ X1 ) @ ( k2_zfmisc_1 @ X0 @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('31',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('32',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['29','32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['3','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BCF58ix9jA
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:25:48 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.30/1.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.30/1.51  % Solved by: fo/fo7.sh
% 1.30/1.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.30/1.51  % done 1349 iterations in 1.069s
% 1.30/1.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.30/1.51  % SZS output start Refutation
% 1.30/1.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.30/1.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.30/1.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.30/1.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.30/1.51  thf(sk_B_type, type, sk_B: $i > $i).
% 1.30/1.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.30/1.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.30/1.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.30/1.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.30/1.51  thf(sk_A_type, type, sk_A: $i).
% 1.30/1.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.30/1.51  thf(l13_xboole_0, axiom,
% 1.30/1.51    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.30/1.51  thf('0', plain,
% 1.30/1.51      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 1.30/1.51      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.30/1.51  thf(t130_zfmisc_1, conjecture,
% 1.30/1.51    (![A:$i,B:$i]:
% 1.30/1.51     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 1.30/1.51       ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 1.30/1.51         ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ))).
% 1.30/1.51  thf(zf_stmt_0, negated_conjecture,
% 1.30/1.51    (~( ![A:$i,B:$i]:
% 1.30/1.51        ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 1.30/1.51          ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 1.30/1.51            ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ) )),
% 1.30/1.51    inference('cnf.neg', [status(esa)], [t130_zfmisc_1])).
% 1.30/1.51  thf('1', plain, (((sk_A) != (k1_xboole_0))),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('2', plain, (![X0 : $i]: (((sk_A) != (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.30/1.51      inference('sup-', [status(thm)], ['0', '1'])).
% 1.30/1.51  thf('3', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.30/1.51      inference('simplify', [status(thm)], ['2'])).
% 1.30/1.51  thf('4', plain,
% 1.30/1.51      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_xboole_0))
% 1.30/1.51        | ((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_xboole_0)))),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('5', plain,
% 1.30/1.51      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_xboole_0)))
% 1.30/1.51         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_xboole_0))))),
% 1.30/1.51      inference('split', [status(esa)], ['4'])).
% 1.30/1.51  thf('6', plain,
% 1.30/1.51      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_xboole_0)))
% 1.30/1.51         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_xboole_0))))),
% 1.30/1.51      inference('split', [status(esa)], ['4'])).
% 1.30/1.51  thf(d1_xboole_0, axiom,
% 1.30/1.51    (![A:$i]:
% 1.30/1.51     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.30/1.51  thf('7', plain,
% 1.30/1.51      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.30/1.51      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.30/1.51  thf(t128_zfmisc_1, axiom,
% 1.30/1.51    (![A:$i,B:$i,C:$i,D:$i]:
% 1.30/1.51     ( ( r2_hidden @
% 1.30/1.51         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 1.30/1.51       ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ))).
% 1.30/1.51  thf('8', plain,
% 1.30/1.51      (![X38 : $i, X39 : $i, X40 : $i, X42 : $i]:
% 1.30/1.51         ((r2_hidden @ (k4_tarski @ X39 @ X40) @ 
% 1.30/1.51           (k2_zfmisc_1 @ (k1_tarski @ X38) @ X42))
% 1.30/1.51          | ~ (r2_hidden @ X40 @ X42)
% 1.30/1.51          | ((X39) != (X38)))),
% 1.30/1.51      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 1.30/1.51  thf('9', plain,
% 1.30/1.51      (![X38 : $i, X40 : $i, X42 : $i]:
% 1.30/1.51         (~ (r2_hidden @ X40 @ X42)
% 1.30/1.51          | (r2_hidden @ (k4_tarski @ X38 @ X40) @ 
% 1.30/1.51             (k2_zfmisc_1 @ (k1_tarski @ X38) @ X42)))),
% 1.30/1.51      inference('simplify', [status(thm)], ['8'])).
% 1.30/1.51  thf('10', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]:
% 1.30/1.51         ((v1_xboole_0 @ X0)
% 1.30/1.51          | (r2_hidden @ (k4_tarski @ X1 @ (sk_B @ X0)) @ 
% 1.30/1.51             (k2_zfmisc_1 @ (k1_tarski @ X1) @ X0)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['7', '9'])).
% 1.30/1.51  thf('11', plain,
% 1.30/1.51      ((((r2_hidden @ (k4_tarski @ sk_B_1 @ (sk_B @ sk_A)) @ k1_xboole_0)
% 1.30/1.51         | (v1_xboole_0 @ sk_A)))
% 1.30/1.51         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_xboole_0))))),
% 1.30/1.51      inference('sup+', [status(thm)], ['6', '10'])).
% 1.30/1.51  thf(t2_boole, axiom,
% 1.30/1.51    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.30/1.51  thf('12', plain,
% 1.30/1.51      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 1.30/1.51      inference('cnf', [status(esa)], [t2_boole])).
% 1.30/1.51  thf(t4_xboole_0, axiom,
% 1.30/1.51    (![A:$i,B:$i]:
% 1.30/1.51     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.30/1.51            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.30/1.51       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.30/1.51            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.30/1.51  thf('13', plain,
% 1.30/1.51      (![X4 : $i, X6 : $i, X7 : $i]:
% 1.30/1.51         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 1.30/1.51          | ~ (r1_xboole_0 @ X4 @ X7))),
% 1.30/1.51      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.30/1.51  thf('14', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]:
% 1.30/1.51         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 1.30/1.51      inference('sup-', [status(thm)], ['12', '13'])).
% 1.30/1.51  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 1.30/1.51  thf('15', plain, (![X9 : $i]: (r1_xboole_0 @ X9 @ k1_xboole_0)),
% 1.30/1.51      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.30/1.51  thf('16', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 1.30/1.51      inference('demod', [status(thm)], ['14', '15'])).
% 1.30/1.51  thf('17', plain,
% 1.30/1.51      (((v1_xboole_0 @ sk_A))
% 1.30/1.51         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_xboole_0))))),
% 1.30/1.51      inference('clc', [status(thm)], ['11', '16'])).
% 1.30/1.51  thf('18', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.30/1.51      inference('simplify', [status(thm)], ['2'])).
% 1.30/1.51  thf('19', plain,
% 1.30/1.51      (~ (((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_xboole_0)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['17', '18'])).
% 1.30/1.51  thf('20', plain,
% 1.30/1.51      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_xboole_0))) | 
% 1.30/1.51       (((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_xboole_0)))),
% 1.30/1.51      inference('split', [status(esa)], ['4'])).
% 1.30/1.51  thf('21', plain,
% 1.30/1.51      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_xboole_0)))),
% 1.30/1.51      inference('sat_resolution*', [status(thm)], ['19', '20'])).
% 1.30/1.51  thf('22', plain,
% 1.30/1.51      (((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_xboole_0))),
% 1.30/1.51      inference('simpl_trail', [status(thm)], ['5', '21'])).
% 1.30/1.51  thf('23', plain,
% 1.30/1.51      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.30/1.51      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.30/1.51  thf(t129_zfmisc_1, axiom,
% 1.30/1.51    (![A:$i,B:$i,C:$i,D:$i]:
% 1.30/1.51     ( ( r2_hidden @
% 1.30/1.51         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 1.30/1.51       ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ))).
% 1.30/1.51  thf('24', plain,
% 1.30/1.51      (![X43 : $i, X44 : $i, X45 : $i, X47 : $i]:
% 1.30/1.51         ((r2_hidden @ (k4_tarski @ X43 @ X45) @ 
% 1.30/1.51           (k2_zfmisc_1 @ X44 @ (k1_tarski @ X47)))
% 1.30/1.51          | ((X45) != (X47))
% 1.30/1.51          | ~ (r2_hidden @ X43 @ X44))),
% 1.30/1.51      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 1.30/1.51  thf('25', plain,
% 1.30/1.51      (![X43 : $i, X44 : $i, X47 : $i]:
% 1.30/1.51         (~ (r2_hidden @ X43 @ X44)
% 1.30/1.51          | (r2_hidden @ (k4_tarski @ X43 @ X47) @ 
% 1.30/1.51             (k2_zfmisc_1 @ X44 @ (k1_tarski @ X47))))),
% 1.30/1.51      inference('simplify', [status(thm)], ['24'])).
% 1.30/1.51  thf('26', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]:
% 1.30/1.51         ((v1_xboole_0 @ X0)
% 1.30/1.51          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ X1) @ 
% 1.30/1.51             (k2_zfmisc_1 @ X0 @ (k1_tarski @ X1))))),
% 1.30/1.51      inference('sup-', [status(thm)], ['23', '25'])).
% 1.30/1.51  thf('27', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.30/1.51      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.30/1.51  thf('28', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]:
% 1.30/1.51         ((v1_xboole_0 @ X1)
% 1.30/1.51          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ (k1_tarski @ X0))))),
% 1.30/1.51      inference('sup-', [status(thm)], ['26', '27'])).
% 1.30/1.51  thf('29', plain, ((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_A))),
% 1.30/1.51      inference('sup-', [status(thm)], ['22', '28'])).
% 1.30/1.51  thf('30', plain,
% 1.30/1.51      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.30/1.51      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.30/1.51  thf('31', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 1.30/1.51      inference('demod', [status(thm)], ['14', '15'])).
% 1.30/1.51  thf('32', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.30/1.51      inference('sup-', [status(thm)], ['30', '31'])).
% 1.30/1.51  thf('33', plain, ((v1_xboole_0 @ sk_A)),
% 1.30/1.51      inference('demod', [status(thm)], ['29', '32'])).
% 1.30/1.51  thf('34', plain, ($false), inference('demod', [status(thm)], ['3', '33'])).
% 1.30/1.51  
% 1.30/1.51  % SZS output end Refutation
% 1.30/1.51  
% 1.30/1.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
