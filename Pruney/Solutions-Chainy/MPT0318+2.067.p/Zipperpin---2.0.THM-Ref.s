%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oql8e86DLn

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:29 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   46 (  64 expanded)
%              Number of leaves         :   17 (  25 expanded)
%              Depth                    :   11
%              Number of atoms          :  319 ( 515 expanded)
%              Number of equality atoms :   34 (  65 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

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

thf('0',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('3',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t128_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) )
    <=> ( ( A = C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('4',plain,(
    ! [X35: $i,X36: $i,X37: $i,X39: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X36 @ X37 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X35 ) @ X39 ) )
      | ~ ( r2_hidden @ X37 @ X39 )
      | ( X36 != X35 ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('5',plain,(
    ! [X35: $i,X37: $i,X39: $i] :
      ( ~ ( r2_hidden @ X37 @ X39 )
      | ( r2_hidden @ ( k4_tarski @ X35 @ X37 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X35 ) @ X39 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_B @ X0 ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ sk_B_1 @ ( sk_B @ sk_A ) ) @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['2','6'])).

thf('8',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B_1 @ ( sk_B @ sk_A ) ) @ k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('10',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
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

thf('11',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('13',plain,(
    ! [X6: $i] :
      ( r1_xboole_0 @ X6 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('14',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('17',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['1','17'])).

thf('19',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t129_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( B = D ) ) ) )).

thf('20',plain,(
    ! [X40: $i,X41: $i,X42: $i,X44: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X40 @ X42 ) @ ( k2_zfmisc_1 @ X41 @ ( k1_tarski @ X44 ) ) )
      | ( X42 != X44 )
      | ~ ( r2_hidden @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('21',plain,(
    ! [X40: $i,X41: $i,X44: $i] :
      ( ~ ( r2_hidden @ X40 @ X41 )
      | ( r2_hidden @ ( k4_tarski @ X40 @ X44 ) @ ( k2_zfmisc_1 @ X41 @ ( k1_tarski @ X44 ) ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ X1 ) @ ( k2_zfmisc_1 @ X0 @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ sk_B_1 ) @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','22'])).

thf('24',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ sk_B_1 ) @ k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('27',plain,(
    $false ),
    inference('sup-',[status(thm)],['25','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oql8e86DLn
% 0.14/0.38  % Computer   : n003.cluster.edu
% 0.14/0.38  % Model      : x86_64 x86_64
% 0.14/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.38  % Memory     : 8042.1875MB
% 0.14/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.38  % CPULimit   : 60
% 0.14/0.38  % DateTime   : Tue Dec  1 09:32:57 EST 2020
% 0.14/0.38  % CPUTime    : 
% 0.14/0.38  % Running portfolio for 600 s
% 0.14/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.35/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.56  % Solved by: fo/fo7.sh
% 0.35/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.56  % done 240 iterations in 0.084s
% 0.35/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.56  % SZS output start Refutation
% 0.35/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.35/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.35/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.35/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.35/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.35/0.56  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.35/0.56  thf(t130_zfmisc_1, conjecture,
% 0.35/0.56    (![A:$i,B:$i]:
% 0.35/0.56     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.35/0.56       ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.35/0.56         ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.35/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.56    (~( ![A:$i,B:$i]:
% 0.35/0.56        ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.35/0.56          ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.35/0.56            ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ) )),
% 0.35/0.56    inference('cnf.neg', [status(esa)], [t130_zfmisc_1])).
% 0.35/0.56  thf('0', plain,
% 0.35/0.56      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_xboole_0))
% 0.35/0.56        | ((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_xboole_0)))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('1', plain,
% 0.35/0.56      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_xboole_0)))
% 0.35/0.56         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_xboole_0))))),
% 0.35/0.56      inference('split', [status(esa)], ['0'])).
% 0.35/0.56  thf('2', plain,
% 0.35/0.56      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_xboole_0)))
% 0.35/0.56         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_xboole_0))))),
% 0.35/0.56      inference('split', [status(esa)], ['0'])).
% 0.35/0.56  thf(t7_xboole_0, axiom,
% 0.35/0.56    (![A:$i]:
% 0.35/0.56     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.35/0.56          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.35/0.56  thf('3', plain,
% 0.35/0.56      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.35/0.56      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.35/0.56  thf(t128_zfmisc_1, axiom,
% 0.35/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.56     ( ( r2_hidden @
% 0.35/0.56         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.35/0.56       ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ))).
% 0.35/0.56  thf('4', plain,
% 0.35/0.56      (![X35 : $i, X36 : $i, X37 : $i, X39 : $i]:
% 0.35/0.56         ((r2_hidden @ (k4_tarski @ X36 @ X37) @ 
% 0.35/0.56           (k2_zfmisc_1 @ (k1_tarski @ X35) @ X39))
% 0.35/0.56          | ~ (r2_hidden @ X37 @ X39)
% 0.35/0.56          | ((X36) != (X35)))),
% 0.35/0.56      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 0.35/0.56  thf('5', plain,
% 0.35/0.56      (![X35 : $i, X37 : $i, X39 : $i]:
% 0.35/0.56         (~ (r2_hidden @ X37 @ X39)
% 0.35/0.56          | (r2_hidden @ (k4_tarski @ X35 @ X37) @ 
% 0.35/0.56             (k2_zfmisc_1 @ (k1_tarski @ X35) @ X39)))),
% 0.35/0.56      inference('simplify', [status(thm)], ['4'])).
% 0.35/0.56  thf('6', plain,
% 0.35/0.56      (![X0 : $i, X1 : $i]:
% 0.35/0.56         (((X0) = (k1_xboole_0))
% 0.35/0.56          | (r2_hidden @ (k4_tarski @ X1 @ (sk_B @ X0)) @ 
% 0.35/0.56             (k2_zfmisc_1 @ (k1_tarski @ X1) @ X0)))),
% 0.35/0.56      inference('sup-', [status(thm)], ['3', '5'])).
% 0.35/0.56  thf('7', plain,
% 0.35/0.56      ((((r2_hidden @ (k4_tarski @ sk_B_1 @ (sk_B @ sk_A)) @ k1_xboole_0)
% 0.35/0.56         | ((sk_A) = (k1_xboole_0))))
% 0.35/0.56         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_xboole_0))))),
% 0.35/0.56      inference('sup+', [status(thm)], ['2', '6'])).
% 0.35/0.56  thf('8', plain, (((sk_A) != (k1_xboole_0))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('9', plain,
% 0.35/0.56      (((r2_hidden @ (k4_tarski @ sk_B_1 @ (sk_B @ sk_A)) @ k1_xboole_0))
% 0.35/0.56         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_xboole_0))))),
% 0.35/0.56      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.35/0.56  thf(t2_boole, axiom,
% 0.35/0.56    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.35/0.56  thf('10', plain,
% 0.35/0.56      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.56      inference('cnf', [status(esa)], [t2_boole])).
% 0.35/0.56  thf(t4_xboole_0, axiom,
% 0.35/0.56    (![A:$i,B:$i]:
% 0.35/0.56     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.35/0.56            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.35/0.56       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.35/0.56            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.35/0.56  thf('11', plain,
% 0.35/0.56      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.35/0.56         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.35/0.56          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.35/0.56      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.35/0.56  thf('12', plain,
% 0.35/0.56      (![X0 : $i, X1 : $i]:
% 0.35/0.56         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.35/0.56      inference('sup-', [status(thm)], ['10', '11'])).
% 0.35/0.56  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.35/0.56  thf('13', plain, (![X6 : $i]: (r1_xboole_0 @ X6 @ k1_xboole_0)),
% 0.35/0.56      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.35/0.56  thf('14', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.35/0.56      inference('demod', [status(thm)], ['12', '13'])).
% 0.35/0.56  thf('15', plain,
% 0.35/0.56      (~ (((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_xboole_0)))),
% 0.35/0.56      inference('sup-', [status(thm)], ['9', '14'])).
% 0.35/0.56  thf('16', plain,
% 0.35/0.56      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_xboole_0))) | 
% 0.35/0.56       (((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_xboole_0)))),
% 0.35/0.56      inference('split', [status(esa)], ['0'])).
% 0.35/0.56  thf('17', plain,
% 0.35/0.56      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_xboole_0)))),
% 0.35/0.56      inference('sat_resolution*', [status(thm)], ['15', '16'])).
% 0.35/0.56  thf('18', plain,
% 0.35/0.56      (((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_xboole_0))),
% 0.35/0.56      inference('simpl_trail', [status(thm)], ['1', '17'])).
% 0.35/0.56  thf('19', plain,
% 0.35/0.56      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.35/0.56      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.35/0.56  thf(t129_zfmisc_1, axiom,
% 0.35/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.56     ( ( r2_hidden @
% 0.35/0.56         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 0.35/0.56       ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ))).
% 0.35/0.56  thf('20', plain,
% 0.35/0.56      (![X40 : $i, X41 : $i, X42 : $i, X44 : $i]:
% 0.35/0.56         ((r2_hidden @ (k4_tarski @ X40 @ X42) @ 
% 0.35/0.56           (k2_zfmisc_1 @ X41 @ (k1_tarski @ X44)))
% 0.35/0.56          | ((X42) != (X44))
% 0.35/0.56          | ~ (r2_hidden @ X40 @ X41))),
% 0.35/0.56      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 0.35/0.56  thf('21', plain,
% 0.35/0.56      (![X40 : $i, X41 : $i, X44 : $i]:
% 0.35/0.56         (~ (r2_hidden @ X40 @ X41)
% 0.35/0.56          | (r2_hidden @ (k4_tarski @ X40 @ X44) @ 
% 0.35/0.56             (k2_zfmisc_1 @ X41 @ (k1_tarski @ X44))))),
% 0.35/0.56      inference('simplify', [status(thm)], ['20'])).
% 0.35/0.56  thf('22', plain,
% 0.35/0.56      (![X0 : $i, X1 : $i]:
% 0.35/0.56         (((X0) = (k1_xboole_0))
% 0.35/0.56          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ X1) @ 
% 0.35/0.56             (k2_zfmisc_1 @ X0 @ (k1_tarski @ X1))))),
% 0.35/0.56      inference('sup-', [status(thm)], ['19', '21'])).
% 0.35/0.56  thf('23', plain,
% 0.35/0.56      (((r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ sk_B_1) @ k1_xboole_0)
% 0.35/0.56        | ((sk_A) = (k1_xboole_0)))),
% 0.35/0.56      inference('sup+', [status(thm)], ['18', '22'])).
% 0.35/0.56  thf('24', plain, (((sk_A) != (k1_xboole_0))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('25', plain,
% 0.35/0.56      ((r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ sk_B_1) @ k1_xboole_0)),
% 0.35/0.56      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.35/0.56  thf('26', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.35/0.56      inference('demod', [status(thm)], ['12', '13'])).
% 0.35/0.56  thf('27', plain, ($false), inference('sup-', [status(thm)], ['25', '26'])).
% 0.35/0.56  
% 0.35/0.56  % SZS output end Refutation
% 0.35/0.56  
% 0.35/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
