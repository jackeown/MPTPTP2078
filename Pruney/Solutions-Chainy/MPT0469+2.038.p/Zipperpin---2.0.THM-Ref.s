%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fEm0nkR8wB

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:21 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 100 expanded)
%              Number of leaves         :   18 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :  243 ( 574 expanded)
%              Number of equality atoms :   31 (  51 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i )).

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

thf('0',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X23: $i] :
      ( ( X23
        = ( k1_relat_1 @ X20 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X23 @ X20 ) @ ( sk_D_1 @ X23 @ X20 ) ) @ X20 )
      | ( r2_hidden @ ( sk_C_1 @ X23 @ X20 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('3',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X11 ) @ X12 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('8',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('13',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['11','12'])).

thf('14',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['1','13'])).

thf('15',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('17',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) ) ) )).

thf('19',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X25 ) @ ( k1_relat_1 @ X25 ) )
      | ~ ( r2_hidden @ X26 @ ( k2_relat_1 @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t19_relat_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r2_hidden @ ( sk_C_2 @ k1_xboole_0 ) @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','20'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('22',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ X15 )
      | ( r2_hidden @ ( sk_B @ X15 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('23',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('24',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r2_hidden @ ( sk_C_2 @ k1_xboole_0 ) @ k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('27',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['14','27'])).

thf('29',plain,(
    $false ),
    inference(simplify,[status(thm)],['28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fEm0nkR8wB
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:47:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 38 iterations in 0.021s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.47  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.19/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.47  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.47  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.19/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.47  thf(sk_C_2_type, type, sk_C_2: $i > $i).
% 0.19/0.47  thf(t60_relat_1, conjecture,
% 0.19/0.47    (( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.19/0.47     ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (~( ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.19/0.47        ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t60_relat_1])).
% 0.19/0.47  thf('0', plain,
% 0.19/0.47      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.19/0.47        | ((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('1', plain,
% 0.19/0.47      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.19/0.47         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.19/0.47      inference('split', [status(esa)], ['0'])).
% 0.19/0.47  thf(d4_relat_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.19/0.47       ( ![C:$i]:
% 0.19/0.47         ( ( r2_hidden @ C @ B ) <=>
% 0.19/0.47           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.19/0.47  thf('2', plain,
% 0.19/0.47      (![X20 : $i, X23 : $i]:
% 0.19/0.47         (((X23) = (k1_relat_1 @ X20))
% 0.19/0.47          | (r2_hidden @ 
% 0.19/0.47             (k4_tarski @ (sk_C_1 @ X23 @ X20) @ (sk_D_1 @ X23 @ X20)) @ X20)
% 0.19/0.47          | (r2_hidden @ (sk_C_1 @ X23 @ X20) @ X23))),
% 0.19/0.47      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.19/0.47  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.19/0.47  thf('3', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.19/0.47      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.19/0.47  thf(l24_zfmisc_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.19/0.47  thf('4', plain,
% 0.19/0.47      (![X11 : $i, X12 : $i]:
% 0.19/0.47         (~ (r1_xboole_0 @ (k1_tarski @ X11) @ X12) | ~ (r2_hidden @ X11 @ X12))),
% 0.19/0.47      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.19/0.47  thf('5', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.19/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.47  thf('6', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.19/0.47          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['2', '5'])).
% 0.19/0.47  thf('7', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.19/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.47  thf('8', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.47  thf('9', plain,
% 0.19/0.47      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.19/0.47         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.19/0.47      inference('split', [status(esa)], ['0'])).
% 0.19/0.47  thf('10', plain,
% 0.19/0.47      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.19/0.47         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.19/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.47  thf('11', plain, ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.19/0.47      inference('simplify', [status(thm)], ['10'])).
% 0.19/0.47  thf('12', plain,
% 0.19/0.47      (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.19/0.47       ~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.19/0.47      inference('split', [status(esa)], ['0'])).
% 0.19/0.47  thf('13', plain, (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.19/0.47      inference('sat_resolution*', [status(thm)], ['11', '12'])).
% 0.19/0.47  thf('14', plain, (((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.19/0.47      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.19/0.47  thf('15', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.47  thf('16', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.19/0.47          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['2', '5'])).
% 0.19/0.47  thf('17', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.47  thf('18', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.19/0.47          | ((X0) = (k1_xboole_0)))),
% 0.19/0.47      inference('demod', [status(thm)], ['16', '17'])).
% 0.19/0.47  thf(t19_relat_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( v1_relat_1 @ B ) =>
% 0.19/0.47       ( ~( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) & 
% 0.19/0.47            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 0.19/0.47  thf('19', plain,
% 0.19/0.47      (![X25 : $i, X26 : $i]:
% 0.19/0.47         ((r2_hidden @ (sk_C_2 @ X25) @ (k1_relat_1 @ X25))
% 0.19/0.47          | ~ (r2_hidden @ X26 @ (k2_relat_1 @ X25))
% 0.19/0.47          | ~ (v1_relat_1 @ X25))),
% 0.19/0.47      inference('cnf', [status(esa)], [t19_relat_1])).
% 0.19/0.47  thf('20', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.19/0.47          | ~ (v1_relat_1 @ X0)
% 0.19/0.47          | (r2_hidden @ (sk_C_2 @ X0) @ (k1_relat_1 @ X0)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.47  thf('21', plain,
% 0.19/0.47      (((r2_hidden @ (sk_C_2 @ k1_xboole_0) @ k1_xboole_0)
% 0.19/0.47        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.19/0.47        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.19/0.47      inference('sup+', [status(thm)], ['15', '20'])).
% 0.19/0.47  thf(d1_relat_1, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( v1_relat_1 @ A ) <=>
% 0.19/0.47       ( ![B:$i]:
% 0.19/0.47         ( ~( ( r2_hidden @ B @ A ) & 
% 0.19/0.47              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.19/0.47  thf('22', plain,
% 0.19/0.47      (![X15 : $i]: ((v1_relat_1 @ X15) | (r2_hidden @ (sk_B @ X15) @ X15))),
% 0.19/0.47      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.19/0.47  thf('23', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.19/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.47  thf('24', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.19/0.47      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.47  thf('25', plain,
% 0.19/0.47      (((r2_hidden @ (sk_C_2 @ k1_xboole_0) @ k1_xboole_0)
% 0.19/0.47        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.19/0.47      inference('demod', [status(thm)], ['21', '24'])).
% 0.19/0.47  thf('26', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.19/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.47  thf('27', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.47      inference('clc', [status(thm)], ['25', '26'])).
% 0.19/0.47  thf('28', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.19/0.47      inference('demod', [status(thm)], ['14', '27'])).
% 0.19/0.47  thf('29', plain, ($false), inference('simplify', [status(thm)], ['28'])).
% 0.19/0.47  
% 0.19/0.47  % SZS output end Refutation
% 0.19/0.47  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
