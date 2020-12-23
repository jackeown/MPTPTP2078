%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.z8fRVYsuQT

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:26 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   50 (  68 expanded)
%              Number of leaves         :   19 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :  272 ( 411 expanded)
%              Number of equality atoms :   37 (  65 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('0',plain,(
    ! [X8: $i,X11: $i] :
      ( ( X11
        = ( k2_relat_1 @ X8 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X11 @ X8 ) @ ( sk_C @ X11 @ X8 ) ) @ X8 )
      | ( r2_hidden @ ( sk_C @ X11 @ X8 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('2',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ~ ( r2_hidden @ X4 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('7',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

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

thf('8',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k2_relat_1 @ B ) ) ) ) )).

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X15 ) @ ( k2_relat_1 @ X15 ) )
      | ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t18_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X10 @ X8 ) @ X10 ) @ X8 )
      | ( X9
       != ( k2_relat_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('14',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X10 @ X8 ) @ X10 ) @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k2_relat_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_C_1 @ X0 ) @ X0 ) @ ( sk_C_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('17',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('19',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('21',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['17','21'])).

thf('23',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('24',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('27',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['25','26'])).

thf('28',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['9','27'])).

thf('29',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['7','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.z8fRVYsuQT
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:23:02 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 25 iterations in 0.016s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.22/0.48  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.22/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.48  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.22/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.48  thf(d5_relat_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.22/0.48       ( ![C:$i]:
% 0.22/0.48         ( ( r2_hidden @ C @ B ) <=>
% 0.22/0.48           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.22/0.48  thf('0', plain,
% 0.22/0.48      (![X8 : $i, X11 : $i]:
% 0.22/0.48         (((X11) = (k2_relat_1 @ X8))
% 0.22/0.48          | (r2_hidden @ (k4_tarski @ (sk_D @ X11 @ X8) @ (sk_C @ X11 @ X8)) @ 
% 0.22/0.48             X8)
% 0.22/0.48          | (r2_hidden @ (sk_C @ X11 @ X8) @ X11))),
% 0.22/0.48      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.22/0.48  thf(t113_zfmisc_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.48       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.48  thf('1', plain,
% 0.22/0.48      (![X2 : $i, X3 : $i]:
% 0.22/0.48         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 0.22/0.48      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.22/0.48  thf('2', plain,
% 0.22/0.48      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.48      inference('simplify', [status(thm)], ['1'])).
% 0.22/0.48  thf(t152_zfmisc_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.22/0.48  thf('3', plain,
% 0.22/0.48      (![X4 : $i, X5 : $i]: ~ (r2_hidden @ X4 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.22/0.48      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.22/0.48  thf('4', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.22/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.48  thf('5', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.22/0.48          | ((X0) = (k2_relat_1 @ k1_xboole_0)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['0', '4'])).
% 0.22/0.48  thf('6', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.22/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.48  thf('7', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.48  thf(t60_relat_1, conjecture,
% 0.22/0.48    (( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.22/0.48     ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.22/0.48        ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t60_relat_1])).
% 0.22/0.48  thf('8', plain,
% 0.22/0.48      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.22/0.48        | ((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('9', plain,
% 0.22/0.48      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.22/0.48         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.22/0.48      inference('split', [status(esa)], ['8'])).
% 0.22/0.48  thf(t7_xboole_0, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.48          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.22/0.48  thf('10', plain,
% 0.22/0.48      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.22/0.48      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.22/0.48  thf(t18_relat_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( v1_relat_1 @ B ) =>
% 0.22/0.48       ( ~( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) & 
% 0.22/0.48            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.22/0.48  thf('11', plain,
% 0.22/0.48      (![X15 : $i, X16 : $i]:
% 0.22/0.48         ((r2_hidden @ (sk_C_1 @ X15) @ (k2_relat_1 @ X15))
% 0.22/0.48          | ~ (r2_hidden @ X16 @ (k1_relat_1 @ X15))
% 0.22/0.48          | ~ (v1_relat_1 @ X15))),
% 0.22/0.48      inference('cnf', [status(esa)], [t18_relat_1])).
% 0.22/0.48  thf('12', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (((k1_relat_1 @ X0) = (k1_xboole_0))
% 0.22/0.48          | ~ (v1_relat_1 @ X0)
% 0.22/0.48          | (r2_hidden @ (sk_C_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.48  thf('13', plain,
% 0.22/0.48      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.48         (~ (r2_hidden @ X10 @ X9)
% 0.22/0.48          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X10 @ X8) @ X10) @ X8)
% 0.22/0.48          | ((X9) != (k2_relat_1 @ X8)))),
% 0.22/0.48      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.22/0.48  thf('14', plain,
% 0.22/0.48      (![X8 : $i, X10 : $i]:
% 0.22/0.48         ((r2_hidden @ (k4_tarski @ (sk_D_1 @ X10 @ X8) @ X10) @ X8)
% 0.22/0.48          | ~ (r2_hidden @ X10 @ (k2_relat_1 @ X8)))),
% 0.22/0.48      inference('simplify', [status(thm)], ['13'])).
% 0.22/0.48  thf('15', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (v1_relat_1 @ X0)
% 0.22/0.48          | ((k1_relat_1 @ X0) = (k1_xboole_0))
% 0.22/0.48          | (r2_hidden @ 
% 0.22/0.48             (k4_tarski @ (sk_D_1 @ (sk_C_1 @ X0) @ X0) @ (sk_C_1 @ X0)) @ X0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['12', '14'])).
% 0.22/0.48  thf('16', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.22/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.48  thf('17', plain,
% 0.22/0.48      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.22/0.48        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.48  thf('18', plain,
% 0.22/0.48      (![X2 : $i, X3 : $i]:
% 0.22/0.48         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.22/0.48      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.22/0.48  thf('19', plain,
% 0.22/0.48      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.22/0.48      inference('simplify', [status(thm)], ['18'])).
% 0.22/0.48  thf(fc6_relat_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.22/0.48  thf('20', plain,
% 0.22/0.48      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14))),
% 0.22/0.48      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.22/0.48  thf('21', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.48      inference('sup+', [status(thm)], ['19', '20'])).
% 0.22/0.48  thf('22', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.48      inference('demod', [status(thm)], ['17', '21'])).
% 0.22/0.48  thf('23', plain,
% 0.22/0.48      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.22/0.48         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.22/0.48      inference('split', [status(esa)], ['8'])).
% 0.22/0.48  thf('24', plain,
% 0.22/0.48      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.22/0.48         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.22/0.48      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.48  thf('25', plain, ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.22/0.48      inference('simplify', [status(thm)], ['24'])).
% 0.22/0.48  thf('26', plain,
% 0.22/0.48      (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.22/0.48       ~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.22/0.48      inference('split', [status(esa)], ['8'])).
% 0.22/0.48  thf('27', plain, (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.22/0.48      inference('sat_resolution*', [status(thm)], ['25', '26'])).
% 0.22/0.48  thf('28', plain, (((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.48      inference('simpl_trail', [status(thm)], ['9', '27'])).
% 0.22/0.48  thf('29', plain, ($false),
% 0.22/0.48      inference('simplify_reflect-', [status(thm)], ['7', '28'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
