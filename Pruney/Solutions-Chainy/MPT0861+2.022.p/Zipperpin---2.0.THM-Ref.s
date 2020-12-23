%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hpDQJcBjrq

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 (  84 expanded)
%              Number of leaves         :   17 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :  301 ( 801 expanded)
%              Number of equality atoms :   45 ( 116 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(t17_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) )
     => ( ( ( ( k1_mcart_1 @ A )
            = B )
          | ( ( k1_mcart_1 @ A )
            = C ) )
        & ( ( k2_mcart_1 @ A )
          = D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) )
       => ( ( ( ( k1_mcart_1 @ A )
              = B )
            | ( ( k1_mcart_1 @ A )
              = C ) )
          & ( ( k2_mcart_1 @ A )
            = D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_mcart_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X16 ) @ X17 )
      | ~ ( r2_hidden @ X16 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('2',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t136_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != B )
        & ( A != C )
        & ( ( k4_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ A ) )
         != ( k2_tarski @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 = X0 )
      | ( ( k4_xboole_0 @ ( k1_enumset1 @ X1 @ X0 @ X2 ) @ ( k1_tarski @ X1 ) )
        = ( k2_tarski @ X0 @ X2 ) )
      | ( X1 = X2 ) ) ),
    inference(cnf,[status(esa)],[t136_enumset1])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( X12 != X14 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X13 @ ( k1_tarski @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ~ ( r2_hidden @ X14 @ ( k4_xboole_0 @ X13 @ ( k1_tarski @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( X2 = X0 )
      | ( X2 = X1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,
    ( ( ( k1_mcart_1 @ sk_A )
      = sk_B )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_C ) ),
    inference('sup-',[status(thm)],['2','6'])).

thf('8',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X16 ) @ X18 )
      | ~ ( r2_hidden @ X16 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('12',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X10 ) @ ( k1_tarski @ X11 ) )
        = ( k1_tarski @ X10 ) )
      | ( X10 = X11 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ~ ( r2_hidden @ X14 @ ( k4_xboole_0 @ X13 @ ( k1_tarski @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( sk_D
    = ( k2_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,
    ( ( sk_D != sk_D )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_D ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(split,[status(esa)],['8'])).

thf('22',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_C ),
    inference('sat_resolution*',[status(thm)],['20','21'])).

thf('23',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_C ),
    inference(simpl_trail,[status(thm)],['9','22'])).

thf('24',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['17'])).

thf('25',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(split,[status(esa)],['17'])).

thf('26',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['20','25'])).

thf('27',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['24','26'])).

thf('28',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['7','23','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hpDQJcBjrq
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:19:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 106 iterations in 0.063s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.52  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.52  thf(t17_mcart_1, conjecture,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52     ( ( r2_hidden @
% 0.21/0.52         A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) ) =>
% 0.21/0.52       ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.21/0.52         ( ( k2_mcart_1 @ A ) = ( D ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52        ( ( r2_hidden @
% 0.21/0.52            A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) ) =>
% 0.21/0.52          ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.21/0.52            ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t17_mcart_1])).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      ((r2_hidden @ sk_A @ 
% 0.21/0.52        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_D)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t10_mcart_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.21/0.52       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.21/0.52         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.52         ((r2_hidden @ (k1_mcart_1 @ X16) @ X17)
% 0.21/0.52          | ~ (r2_hidden @ X16 @ (k2_zfmisc_1 @ X17 @ X18)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.21/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.52  thf(t136_enumset1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ~( ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) & 
% 0.21/0.52          ( ( k4_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ A ) ) !=
% 0.21/0.52            ( k2_tarski @ B @ C ) ) ) ))).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (((X1) = (X0))
% 0.21/0.52          | ((k4_xboole_0 @ (k1_enumset1 @ X1 @ X0 @ X2) @ (k1_tarski @ X1))
% 0.21/0.52              = (k2_tarski @ X0 @ X2))
% 0.21/0.52          | ((X1) = (X2)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t136_enumset1])).
% 0.21/0.52  thf(t64_zfmisc_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.21/0.52       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.52         (((X12) != (X14))
% 0.21/0.52          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X13 @ (k1_tarski @ X14))))),
% 0.21/0.52      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (![X13 : $i, X14 : $i]:
% 0.21/0.52         ~ (r2_hidden @ X14 @ (k4_xboole_0 @ X13 @ (k1_tarski @ X14)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.21/0.52          | ((X2) = (X0))
% 0.21/0.52          | ((X2) = (X1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['3', '5'])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      ((((k1_mcart_1 @ sk_A) = (sk_B)) | ((k1_mcart_1 @ sk_A) = (sk_C)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '6'])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      ((((k1_mcart_1 @ sk_A) != (sk_C)) | ((k2_mcart_1 @ sk_A) != (sk_D)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      ((((k1_mcart_1 @ sk_A) != (sk_C)))
% 0.21/0.52         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C))))),
% 0.21/0.52      inference('split', [status(esa)], ['8'])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      ((r2_hidden @ sk_A @ 
% 0.21/0.52        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_D)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.52         ((r2_hidden @ (k2_mcart_1 @ X16) @ X18)
% 0.21/0.52          | ~ (r2_hidden @ X16 @ (k2_zfmisc_1 @ X17 @ X18)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.52  thf('12', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k1_tarski @ sk_D))),
% 0.21/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.52  thf(t20_zfmisc_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.52         ( k1_tarski @ A ) ) <=>
% 0.21/0.52       ( ( A ) != ( B ) ) ))).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i]:
% 0.21/0.52         (((k4_xboole_0 @ (k1_tarski @ X10) @ (k1_tarski @ X11))
% 0.21/0.52            = (k1_tarski @ X10))
% 0.21/0.52          | ((X10) = (X11)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      (![X13 : $i, X14 : $i]:
% 0.21/0.52         ~ (r2_hidden @ X14 @ (k4_xboole_0 @ X13 @ (k1_tarski @ X14)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X0) = (X1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.52  thf('16', plain, (((sk_D) = (k2_mcart_1 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['12', '15'])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_D)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      ((((k2_mcart_1 @ sk_A) != (sk_D)))
% 0.21/0.52         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D))))),
% 0.21/0.52      inference('split', [status(esa)], ['17'])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      ((((sk_D) != (sk_D))) <= (~ (((k2_mcart_1 @ sk_A) = (sk_D))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['16', '18'])).
% 0.21/0.52  thf('20', plain, ((((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['19'])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (~ (((k1_mcart_1 @ sk_A) = (sk_C))) | ~ (((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.21/0.52      inference('split', [status(esa)], ['8'])).
% 0.21/0.52  thf('22', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_C)))),
% 0.21/0.52      inference('sat_resolution*', [status(thm)], ['20', '21'])).
% 0.21/0.52  thf('23', plain, (((k1_mcart_1 @ sk_A) != (sk_C))),
% 0.21/0.52      inference('simpl_trail', [status(thm)], ['9', '22'])).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 0.21/0.52         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.21/0.52      inference('split', [status(esa)], ['17'])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | ~ (((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.21/0.52      inference('split', [status(esa)], ['17'])).
% 0.21/0.52  thf('26', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.21/0.52      inference('sat_resolution*', [status(thm)], ['20', '25'])).
% 0.21/0.52  thf('27', plain, (((k1_mcart_1 @ sk_A) != (sk_B))),
% 0.21/0.52      inference('simpl_trail', [status(thm)], ['24', '26'])).
% 0.21/0.52  thf('28', plain, ($false),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['7', '23', '27'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
