%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OUYVtY5sBP

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   42 (  57 expanded)
%              Number of leaves         :   16 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :  294 ( 558 expanded)
%              Number of equality atoms :   49 (  91 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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

thf('0',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X12 ) @ X14 )
      | ~ ( r2_hidden @ X12 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('4',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X7 ) @ ( k1_tarski @ X8 ) )
        = ( k1_tarski @ X7 ) )
      | ( X7 = X8 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ( ( k4_xboole_0 @ X10 @ ( k1_tarski @ X9 ) )
       != X10 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( X0 = X1 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( sk_D
    = ( k2_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ( sk_D != sk_D )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_D ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(split,[status(esa)],['10'])).

thf('15',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t15_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) )
     => ( ( ( ( k1_mcart_1 @ A )
            = B )
          | ( ( k1_mcart_1 @ A )
            = C ) )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ) )).

thf('16',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_mcart_1 @ X16 )
        = X15 )
      | ( ( k1_mcart_1 @ X16 )
        = X17 )
      | ~ ( r2_hidden @ X16 @ ( k2_zfmisc_1 @ ( k2_tarski @ X17 @ X15 ) @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t15_mcart_1])).

thf('17',plain,
    ( ( ( k1_mcart_1 @ sk_A )
      = sk_B )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_C ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,
    ( ( ( sk_C != sk_C )
      | ( ( k1_mcart_1 @ sk_A )
        = sk_B ) )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k1_mcart_1 @ sk_A )
      = sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['10'])).

thf('22',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k1_mcart_1 @ sk_A )
       != sk_C )
      & ( ( k1_mcart_1 @ sk_A )
       != sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k1_mcart_1 @ sk_A )
      = sk_B )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_C ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','13','14','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OUYVtY5sBP
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:33:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 44 iterations in 0.011s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.46  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.46  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.46  thf(t17_mcart_1, conjecture,
% 0.21/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.46     ( ( r2_hidden @
% 0.21/0.46         A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) ) =>
% 0.21/0.46       ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.21/0.46         ( ( k2_mcart_1 @ A ) = ( D ) ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.46        ( ( r2_hidden @
% 0.21/0.46            A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) ) =>
% 0.21/0.46          ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.21/0.46            ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t17_mcart_1])).
% 0.21/0.46  thf('0', plain,
% 0.21/0.46      ((((k1_mcart_1 @ sk_A) != (sk_C)) | ((k2_mcart_1 @ sk_A) != (sk_D)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('1', plain,
% 0.21/0.46      (~ (((k1_mcart_1 @ sk_A) = (sk_C))) | ~ (((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.21/0.46      inference('split', [status(esa)], ['0'])).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      ((r2_hidden @ sk_A @ 
% 0.21/0.46        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_D)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t10_mcart_1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.21/0.46       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.21/0.46         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.21/0.46  thf('3', plain,
% 0.21/0.46      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.46         ((r2_hidden @ (k2_mcart_1 @ X12) @ X14)
% 0.21/0.46          | ~ (r2_hidden @ X12 @ (k2_zfmisc_1 @ X13 @ X14)))),
% 0.21/0.46      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.46  thf('4', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k1_tarski @ sk_D))),
% 0.21/0.46      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.46  thf(t20_zfmisc_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.46         ( k1_tarski @ A ) ) <=>
% 0.21/0.46       ( ( A ) != ( B ) ) ))).
% 0.21/0.46  thf('5', plain,
% 0.21/0.46      (![X7 : $i, X8 : $i]:
% 0.21/0.46         (((k4_xboole_0 @ (k1_tarski @ X7) @ (k1_tarski @ X8))
% 0.21/0.46            = (k1_tarski @ X7))
% 0.21/0.46          | ((X7) = (X8)))),
% 0.21/0.46      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.21/0.46  thf(t65_zfmisc_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.21/0.46       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.21/0.46  thf('6', plain,
% 0.21/0.46      (![X9 : $i, X10 : $i]:
% 0.21/0.46         (~ (r2_hidden @ X9 @ X10)
% 0.21/0.46          | ((k4_xboole_0 @ X10 @ (k1_tarski @ X9)) != (X10)))),
% 0.21/0.46      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.21/0.46          | ((X0) = (X1))
% 0.21/0.46          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.46  thf('8', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X0) = (X1)))),
% 0.21/0.46      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.46  thf('9', plain, (((sk_D) = (k2_mcart_1 @ sk_A))),
% 0.21/0.46      inference('sup-', [status(thm)], ['4', '8'])).
% 0.21/0.46  thf('10', plain,
% 0.21/0.46      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_D)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('11', plain,
% 0.21/0.46      ((((k2_mcart_1 @ sk_A) != (sk_D)))
% 0.21/0.46         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D))))),
% 0.21/0.46      inference('split', [status(esa)], ['10'])).
% 0.21/0.46  thf('12', plain,
% 0.21/0.46      ((((sk_D) != (sk_D))) <= (~ (((k2_mcart_1 @ sk_A) = (sk_D))))),
% 0.21/0.46      inference('sup-', [status(thm)], ['9', '11'])).
% 0.21/0.46  thf('13', plain, ((((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.21/0.46      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.46  thf('14', plain,
% 0.21/0.46      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | ~ (((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.21/0.46      inference('split', [status(esa)], ['10'])).
% 0.21/0.46  thf('15', plain,
% 0.21/0.46      ((r2_hidden @ sk_A @ 
% 0.21/0.46        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_D)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t15_mcart_1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.46     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) ) =>
% 0.21/0.46       ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.21/0.46         ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ))).
% 0.21/0.46  thf('16', plain,
% 0.21/0.46      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.46         (((k1_mcart_1 @ X16) = (X15))
% 0.21/0.46          | ((k1_mcart_1 @ X16) = (X17))
% 0.21/0.46          | ~ (r2_hidden @ X16 @ (k2_zfmisc_1 @ (k2_tarski @ X17 @ X15) @ X18)))),
% 0.21/0.46      inference('cnf', [status(esa)], [t15_mcart_1])).
% 0.21/0.46  thf('17', plain,
% 0.21/0.46      ((((k1_mcart_1 @ sk_A) = (sk_B)) | ((k1_mcart_1 @ sk_A) = (sk_C)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.46  thf('18', plain,
% 0.21/0.46      ((((k1_mcart_1 @ sk_A) != (sk_C)))
% 0.21/0.46         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C))))),
% 0.21/0.46      inference('split', [status(esa)], ['0'])).
% 0.21/0.46  thf('19', plain,
% 0.21/0.46      (((((sk_C) != (sk_C)) | ((k1_mcart_1 @ sk_A) = (sk_B))))
% 0.21/0.46         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C))))),
% 0.21/0.46      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.46  thf('20', plain,
% 0.21/0.46      ((((k1_mcart_1 @ sk_A) = (sk_B))) <= (~ (((k1_mcart_1 @ sk_A) = (sk_C))))),
% 0.21/0.46      inference('simplify', [status(thm)], ['19'])).
% 0.21/0.46  thf('21', plain,
% 0.21/0.46      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 0.21/0.46         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.21/0.46      inference('split', [status(esa)], ['10'])).
% 0.21/0.46  thf('22', plain,
% 0.21/0.46      ((((sk_B) != (sk_B)))
% 0.21/0.46         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C))) & 
% 0.21/0.46             ~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.21/0.46      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.46  thf('23', plain,
% 0.21/0.46      ((((k1_mcart_1 @ sk_A) = (sk_B))) | (((k1_mcart_1 @ sk_A) = (sk_C)))),
% 0.21/0.46      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.46  thf('24', plain, ($false),
% 0.21/0.46      inference('sat_resolution*', [status(thm)], ['1', '13', '14', '23'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
