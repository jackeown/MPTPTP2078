%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KjnSE5DMBw

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 104 expanded)
%              Number of leaves         :   21 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :  289 ( 611 expanded)
%              Number of equality atoms :   39 (  91 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('0',plain,(
    ! [X12: $i,X15: $i] :
      ( ( X15
        = ( k1_relat_1 @ X12 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X15 @ X12 ) @ ( sk_D @ X15 @ X12 ) ) @ X12 )
      | ( r2_hidden @ ( sk_C @ X15 @ X12 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('2',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i] :
      ~ ( r2_hidden @ X7 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
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

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('8',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) ) ) )).

thf('9',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X17 ) @ ( k1_relat_1 @ X17 ) )
      | ~ ( r2_hidden @ X18 @ ( k2_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t19_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 ) @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('12',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('14',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','13'])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('15',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('16',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 ) @ k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','16'])).

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

thf('18',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('21',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('25',plain,
    ( ! [X0: $i] :
        ( ( ( k1_relat_1 @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('28',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('31',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['29','30'])).

thf('32',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['19','31'])).

thf('33',plain,(
    r2_hidden @ ( sk_C_1 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['17','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('35',plain,(
    $false ),
    inference('sup-',[status(thm)],['33','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KjnSE5DMBw
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:23:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 122 iterations in 0.060s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.21/0.52  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.52  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.21/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.52  thf(d4_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.21/0.52       ( ![C:$i]:
% 0.21/0.52         ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.52           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      (![X12 : $i, X15 : $i]:
% 0.21/0.52         (((X15) = (k1_relat_1 @ X12))
% 0.21/0.52          | (r2_hidden @ 
% 0.21/0.52             (k4_tarski @ (sk_C @ X15 @ X12) @ (sk_D @ X15 @ X12)) @ X12)
% 0.21/0.52          | (r2_hidden @ (sk_C @ X15 @ X12) @ X15))),
% 0.21/0.52      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.21/0.52  thf(t113_zfmisc_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.52       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      (![X5 : $i, X6 : $i]:
% 0.21/0.52         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.52      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.52  thf(t152_zfmisc_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X7 : $i, X8 : $i]: ~ (r2_hidden @ X7 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.21/0.52      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.21/0.52  thf('4', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.21/0.52          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['0', '4'])).
% 0.21/0.52  thf('6', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.52  thf('7', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.52  thf(t7_xboole_0, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.52          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X3 : $i]: (((X3) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X3) @ X3))),
% 0.21/0.52      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.52  thf(t19_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ B ) =>
% 0.21/0.52       ( ~( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) & 
% 0.21/0.52            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (![X17 : $i, X18 : $i]:
% 0.21/0.53         ((r2_hidden @ (sk_C_1 @ X17) @ (k1_relat_1 @ X17))
% 0.21/0.53          | ~ (r2_hidden @ X18 @ (k2_relat_1 @ X17))
% 0.21/0.53          | ~ (v1_relat_1 @ X17))),
% 0.21/0.53      inference('cnf', [status(esa)], [t19_relat_1])).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.21/0.53          | ~ (v1_relat_1 @ X0)
% 0.21/0.53          | (r2_hidden @ (sk_C_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (((r2_hidden @ (sk_C_1 @ k1_xboole_0) @ k1_xboole_0)
% 0.21/0.53        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.53        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['7', '10'])).
% 0.21/0.53  thf(d1_xboole_0, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.53      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.53  thf('13', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.53  thf('14', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.53  thf(cc1_relat_1, axiom,
% 0.21/0.53    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.21/0.53  thf('15', plain, (![X9 : $i]: ((v1_relat_1 @ X9) | ~ (v1_xboole_0 @ X9))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.21/0.53  thf('16', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      (((r2_hidden @ (sk_C_1 @ k1_xboole_0) @ k1_xboole_0)
% 0.21/0.53        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.53      inference('demod', [status(thm)], ['11', '16'])).
% 0.21/0.53  thf(t60_relat_1, conjecture,
% 0.21/0.53    (( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.53     ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.53        ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t60_relat_1])).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.21/0.53        | ((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.53         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.53      inference('split', [status(esa)], ['18'])).
% 0.21/0.53  thf('20', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      (![X3 : $i]: (((X3) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X3) @ X3))),
% 0.21/0.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.53  thf('24', plain,
% 0.21/0.53      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.53         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.53      inference('split', [status(esa)], ['18'])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      ((![X0 : $i]:
% 0.21/0.53          (((k1_relat_1 @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.21/0.53         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.21/0.53         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['20', '25'])).
% 0.21/0.53  thf('27', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.53         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.53      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.53  thf('29', plain, ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.21/0.53       ~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.53      inference('split', [status(esa)], ['18'])).
% 0.21/0.53  thf('31', plain, (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['29', '30'])).
% 0.21/0.53  thf('32', plain, (((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['19', '31'])).
% 0.21/0.53  thf('33', plain, ((r2_hidden @ (sk_C_1 @ k1_xboole_0) @ k1_xboole_0)),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['17', '32'])).
% 0.21/0.53  thf('34', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.53  thf('35', plain, ($false), inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
