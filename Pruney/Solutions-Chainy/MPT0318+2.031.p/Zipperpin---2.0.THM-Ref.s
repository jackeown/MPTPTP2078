%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Uv6TotbopM

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:25 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   45 (  60 expanded)
%              Number of leaves         :   13 (  21 expanded)
%              Depth                    :   13
%              Number of atoms          :  358 ( 552 expanded)
%              Number of equality atoms :   66 ( 104 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X2 != X1 )
      | ( r2_hidden @ X2 @ X3 )
      | ( X3
       != ( k2_tarski @ X4 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('1',plain,(
    ! [X1: $i,X4: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X4 @ X1 ) ) ),
    inference(simplify,[status(thm)],['0'])).

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

thf('2',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( X14 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X14 @ X13 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('5',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('9',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ( ( k4_xboole_0 @ X17 @ ( k1_tarski @ X16 ) )
       != X17 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('10',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
         != X0 )
        | ~ ( r2_hidden @ sk_B @ X0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('12',plain,
    ( ! [X0: $i] :
        ( ( X0 != X0 )
        | ~ ( r2_hidden @ sk_B @ X0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ sk_B @ X0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X1: $i,X4: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X4 @ X1 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('15',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( X14 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X14 @ X13 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('17',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ( ( k4_xboole_0 @ X17 @ ( k1_tarski @ X16 ) )
       != X17 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('22',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
         != X0 )
        | ~ ( r2_hidden @ sk_B @ X0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ( X0 != X0 )
        | ~ ( r2_hidden @ sk_B @ X0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ sk_B @ X0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['14','25'])).

thf('27',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('28',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_B @ X0 ) ),
    inference(simpl_trail,[status(thm)],['13','28'])).

thf('30',plain,(
    $false ),
    inference('sup-',[status(thm)],['1','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Uv6TotbopM
% 0.12/0.32  % Computer   : n023.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 19:49:06 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running portfolio for 600 s
% 0.12/0.32  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.32  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.18/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.18/0.46  % Solved by: fo/fo7.sh
% 0.18/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.46  % done 31 iterations in 0.015s
% 0.18/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.18/0.46  % SZS output start Refutation
% 0.18/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.18/0.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.18/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.18/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.18/0.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.18/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.18/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.46  thf(d2_tarski, axiom,
% 0.18/0.46    (![A:$i,B:$i,C:$i]:
% 0.18/0.46     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.18/0.46       ( ![D:$i]:
% 0.18/0.46         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.18/0.46  thf('0', plain,
% 0.18/0.46      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.18/0.46         (((X2) != (X1))
% 0.18/0.46          | (r2_hidden @ X2 @ X3)
% 0.18/0.46          | ((X3) != (k2_tarski @ X4 @ X1)))),
% 0.18/0.46      inference('cnf', [status(esa)], [d2_tarski])).
% 0.18/0.46  thf('1', plain,
% 0.18/0.46      (![X1 : $i, X4 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X4 @ X1))),
% 0.18/0.46      inference('simplify', [status(thm)], ['0'])).
% 0.18/0.46  thf(t130_zfmisc_1, conjecture,
% 0.18/0.46    (![A:$i,B:$i]:
% 0.18/0.46     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.18/0.46       ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.18/0.46         ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.18/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.46    (~( ![A:$i,B:$i]:
% 0.18/0.46        ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.18/0.46          ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.18/0.46            ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ) )),
% 0.18/0.46    inference('cnf.neg', [status(esa)], [t130_zfmisc_1])).
% 0.18/0.46  thf('2', plain,
% 0.18/0.46      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))
% 0.18/0.46        | ((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('3', plain,
% 0.18/0.46      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))
% 0.18/0.46         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.18/0.46      inference('split', [status(esa)], ['2'])).
% 0.18/0.46  thf(t113_zfmisc_1, axiom,
% 0.18/0.46    (![A:$i,B:$i]:
% 0.18/0.46     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.18/0.46       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.18/0.46  thf('4', plain,
% 0.18/0.46      (![X13 : $i, X14 : $i]:
% 0.18/0.46         (((X13) = (k1_xboole_0))
% 0.18/0.46          | ((X14) = (k1_xboole_0))
% 0.18/0.46          | ((k2_zfmisc_1 @ X14 @ X13) != (k1_xboole_0)))),
% 0.18/0.46      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.18/0.46  thf('5', plain,
% 0.18/0.46      (((((k1_xboole_0) != (k1_xboole_0))
% 0.18/0.46         | ((sk_A) = (k1_xboole_0))
% 0.18/0.46         | ((k1_tarski @ sk_B) = (k1_xboole_0))))
% 0.18/0.46         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.18/0.46      inference('sup-', [status(thm)], ['3', '4'])).
% 0.18/0.46  thf('6', plain,
% 0.18/0.46      (((((k1_tarski @ sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.18/0.46         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.18/0.46      inference('simplify', [status(thm)], ['5'])).
% 0.18/0.46  thf('7', plain, (((sk_A) != (k1_xboole_0))),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('8', plain,
% 0.18/0.46      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.18/0.46         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.18/0.46      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.18/0.46  thf(t65_zfmisc_1, axiom,
% 0.18/0.46    (![A:$i,B:$i]:
% 0.18/0.46     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.18/0.46       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.18/0.46  thf('9', plain,
% 0.18/0.46      (![X16 : $i, X17 : $i]:
% 0.18/0.46         (~ (r2_hidden @ X16 @ X17)
% 0.18/0.46          | ((k4_xboole_0 @ X17 @ (k1_tarski @ X16)) != (X17)))),
% 0.18/0.46      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.18/0.46  thf('10', plain,
% 0.18/0.46      ((![X0 : $i]:
% 0.18/0.46          (((k4_xboole_0 @ X0 @ k1_xboole_0) != (X0))
% 0.18/0.46           | ~ (r2_hidden @ sk_B @ X0)))
% 0.18/0.46         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.18/0.46      inference('sup-', [status(thm)], ['8', '9'])).
% 0.18/0.46  thf(t3_boole, axiom,
% 0.18/0.46    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.18/0.46  thf('11', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.18/0.46      inference('cnf', [status(esa)], [t3_boole])).
% 0.18/0.46  thf('12', plain,
% 0.18/0.46      ((![X0 : $i]: (((X0) != (X0)) | ~ (r2_hidden @ sk_B @ X0)))
% 0.18/0.46         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.18/0.46      inference('demod', [status(thm)], ['10', '11'])).
% 0.18/0.46  thf('13', plain,
% 0.18/0.46      ((![X0 : $i]: ~ (r2_hidden @ sk_B @ X0))
% 0.18/0.46         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.18/0.46      inference('simplify', [status(thm)], ['12'])).
% 0.18/0.46  thf('14', plain,
% 0.18/0.46      (![X1 : $i, X4 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X4 @ X1))),
% 0.18/0.46      inference('simplify', [status(thm)], ['0'])).
% 0.18/0.46  thf('15', plain,
% 0.18/0.46      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))
% 0.18/0.46         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.18/0.46      inference('split', [status(esa)], ['2'])).
% 0.18/0.46  thf('16', plain,
% 0.18/0.46      (![X13 : $i, X14 : $i]:
% 0.18/0.46         (((X13) = (k1_xboole_0))
% 0.18/0.46          | ((X14) = (k1_xboole_0))
% 0.18/0.46          | ((k2_zfmisc_1 @ X14 @ X13) != (k1_xboole_0)))),
% 0.18/0.46      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.18/0.46  thf('17', plain,
% 0.18/0.46      (((((k1_xboole_0) != (k1_xboole_0))
% 0.18/0.46         | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.18/0.46         | ((sk_A) = (k1_xboole_0))))
% 0.18/0.46         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.18/0.46      inference('sup-', [status(thm)], ['15', '16'])).
% 0.18/0.46  thf('18', plain,
% 0.18/0.46      (((((sk_A) = (k1_xboole_0)) | ((k1_tarski @ sk_B) = (k1_xboole_0))))
% 0.18/0.46         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.18/0.46      inference('simplify', [status(thm)], ['17'])).
% 0.18/0.46  thf('19', plain, (((sk_A) != (k1_xboole_0))),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('20', plain,
% 0.18/0.46      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.18/0.46         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.18/0.46      inference('simplify_reflect-', [status(thm)], ['18', '19'])).
% 0.18/0.46  thf('21', plain,
% 0.18/0.46      (![X16 : $i, X17 : $i]:
% 0.18/0.46         (~ (r2_hidden @ X16 @ X17)
% 0.18/0.46          | ((k4_xboole_0 @ X17 @ (k1_tarski @ X16)) != (X17)))),
% 0.18/0.46      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.18/0.46  thf('22', plain,
% 0.18/0.46      ((![X0 : $i]:
% 0.18/0.46          (((k4_xboole_0 @ X0 @ k1_xboole_0) != (X0))
% 0.18/0.46           | ~ (r2_hidden @ sk_B @ X0)))
% 0.18/0.46         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.18/0.46      inference('sup-', [status(thm)], ['20', '21'])).
% 0.18/0.46  thf('23', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.18/0.46      inference('cnf', [status(esa)], [t3_boole])).
% 0.18/0.46  thf('24', plain,
% 0.18/0.46      ((![X0 : $i]: (((X0) != (X0)) | ~ (r2_hidden @ sk_B @ X0)))
% 0.18/0.46         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.18/0.46      inference('demod', [status(thm)], ['22', '23'])).
% 0.18/0.46  thf('25', plain,
% 0.18/0.46      ((![X0 : $i]: ~ (r2_hidden @ sk_B @ X0))
% 0.18/0.46         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.18/0.46      inference('simplify', [status(thm)], ['24'])).
% 0.18/0.46  thf('26', plain,
% 0.18/0.46      (~ (((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))),
% 0.18/0.46      inference('sup-', [status(thm)], ['14', '25'])).
% 0.18/0.46  thf('27', plain,
% 0.18/0.46      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))) | 
% 0.18/0.46       (((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))),
% 0.18/0.46      inference('split', [status(esa)], ['2'])).
% 0.18/0.46  thf('28', plain,
% 0.18/0.46      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))),
% 0.18/0.46      inference('sat_resolution*', [status(thm)], ['26', '27'])).
% 0.18/0.46  thf('29', plain, (![X0 : $i]: ~ (r2_hidden @ sk_B @ X0)),
% 0.18/0.46      inference('simpl_trail', [status(thm)], ['13', '28'])).
% 0.18/0.46  thf('30', plain, ($false), inference('sup-', [status(thm)], ['1', '29'])).
% 0.18/0.46  
% 0.18/0.46  % SZS output end Refutation
% 0.18/0.46  
% 0.18/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
