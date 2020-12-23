%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7CxjUbPslp

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 (  87 expanded)
%              Number of leaves         :   18 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :  268 ( 542 expanded)
%              Number of equality atoms :   37 (  85 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('0',plain,(
    ! [X9: $i,X12: $i] :
      ( ( X12
        = ( k1_relat_1 @ X9 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X12 @ X9 ) @ ( sk_D @ X12 @ X9 ) ) @ X9 )
      | ( r2_hidden @ ( sk_C_1 @ X12 @ X9 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('2',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ~ ( r2_hidden @ X5 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('7',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('9',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) ) ) )).

thf('11',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X16 ) @ ( k1_relat_1 @ X16 ) )
      | ~ ( r2_hidden @ X17 @ ( k2_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t19_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r2_hidden @ ( sk_C_2 @ k1_xboole_0 ) @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('15',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('16',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('17',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r2_hidden @ ( sk_C_2 @ k1_xboole_0 ) @ k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','17'])).

thf(t60_relat_1,conjecture,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      & ( ( k2_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t60_relat_1])).

thf('19',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('22',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf('23',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['19'])).

thf('26',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['24','25'])).

thf('27',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['20','26'])).

thf('28',plain,(
    r2_hidden @ ( sk_C_2 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['18','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('30',plain,(
    $false ),
    inference('sup-',[status(thm)],['28','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7CxjUbPslp
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:21:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 28 iterations in 0.020s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.47  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.21/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.47  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.21/0.47  thf(sk_C_2_type, type, sk_C_2: $i > $i).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(d4_relat_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.21/0.47       ( ![C:$i]:
% 0.21/0.47         ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.47           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      (![X9 : $i, X12 : $i]:
% 0.21/0.47         (((X12) = (k1_relat_1 @ X9))
% 0.21/0.47          | (r2_hidden @ 
% 0.21/0.47             (k4_tarski @ (sk_C_1 @ X12 @ X9) @ (sk_D @ X12 @ X9)) @ X9)
% 0.21/0.47          | (r2_hidden @ (sk_C_1 @ X12 @ X9) @ X12))),
% 0.21/0.47      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.21/0.47  thf(t113_zfmisc_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.47       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X3 : $i, X4 : $i]:
% 0.21/0.47         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X3 : $i]: ((k2_zfmisc_1 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.47      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.47  thf(t152_zfmisc_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X5 : $i, X6 : $i]: ~ (r2_hidden @ X5 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.21/0.47  thf('4', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.21/0.47          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '4'])).
% 0.21/0.47  thf('6', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.47  thf('7', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.47  thf(t2_tarski, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.21/0.47       ( ( A ) = ( B ) ) ))).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (((X1) = (X0))
% 0.21/0.47          | (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.21/0.47          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.21/0.47      inference('cnf', [status(esa)], [t2_tarski])).
% 0.21/0.47  thf('9', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ X0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.47  thf(t19_relat_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ B ) =>
% 0.21/0.47       ( ~( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) & 
% 0.21/0.47            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X16 : $i, X17 : $i]:
% 0.21/0.47         ((r2_hidden @ (sk_C_2 @ X16) @ (k1_relat_1 @ X16))
% 0.21/0.47          | ~ (r2_hidden @ X17 @ (k2_relat_1 @ X16))
% 0.21/0.47          | ~ (v1_relat_1 @ X16))),
% 0.21/0.47      inference('cnf', [status(esa)], [t19_relat_1])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.21/0.47          | ~ (v1_relat_1 @ X0)
% 0.21/0.47          | (r2_hidden @ (sk_C_2 @ X0) @ (k1_relat_1 @ X0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (((r2_hidden @ (sk_C_2 @ k1_xboole_0) @ k1_xboole_0)
% 0.21/0.47        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.47        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.47      inference('sup+', [status(thm)], ['7', '12'])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (![X3 : $i, X4 : $i]:
% 0.21/0.47         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 0.21/0.47      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.47  thf(fc6_relat_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X14 @ X15))),
% 0.21/0.47      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.47  thf('17', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.47      inference('sup+', [status(thm)], ['15', '16'])).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      (((r2_hidden @ (sk_C_2 @ k1_xboole_0) @ k1_xboole_0)
% 0.21/0.47        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.47      inference('demod', [status(thm)], ['13', '17'])).
% 0.21/0.47  thf(t60_relat_1, conjecture,
% 0.21/0.47    (( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.47     ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.47        ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t60_relat_1])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.21/0.47        | ((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.47         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.47      inference('split', [status(esa)], ['19'])).
% 0.21/0.47  thf('21', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.47  thf('22', plain,
% 0.21/0.47      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.47         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.47      inference('split', [status(esa)], ['19'])).
% 0.21/0.47  thf('23', plain,
% 0.21/0.47      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.47         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.47  thf('24', plain, ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.47      inference('simplify', [status(thm)], ['23'])).
% 0.21/0.47  thf('25', plain,
% 0.21/0.47      (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.21/0.47       ~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.47      inference('split', [status(esa)], ['19'])).
% 0.21/0.47  thf('26', plain, (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.47      inference('sat_resolution*', [status(thm)], ['24', '25'])).
% 0.21/0.47  thf('27', plain, (((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.47      inference('simpl_trail', [status(thm)], ['20', '26'])).
% 0.21/0.47  thf('28', plain, ((r2_hidden @ (sk_C_2 @ k1_xboole_0) @ k1_xboole_0)),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['18', '27'])).
% 0.21/0.47  thf('29', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.47  thf('30', plain, ($false), inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
