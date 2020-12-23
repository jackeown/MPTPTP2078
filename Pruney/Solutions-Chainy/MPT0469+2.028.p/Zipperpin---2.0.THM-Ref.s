%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bc1HP6Z1ev

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:20 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   50 (  97 expanded)
%              Number of leaves         :   19 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  238 ( 549 expanded)
%              Number of equality atoms :   31 (  51 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('2',plain,(
    ! [X21: $i,X24: $i] :
      ( ( X24
        = ( k2_relat_1 @ X21 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X24 @ X21 ) @ ( sk_C @ X24 @ X21 ) ) @ X21 )
      | ( r2_hidden @ ( sk_C @ X24 @ X21 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

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
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X16 ) @ X17 )
      | ~ ( r2_hidden @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('8',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('13',plain,(
    ( k1_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['11','12'])).

thf('14',plain,(
    ( k1_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['1','13'])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('15',plain,(
    ! [X18: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('16',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('18',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k2_relat_1 @ B ) ) ) ) )).

thf('20',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X26 ) @ ( k2_relat_1 @ X26 ) )
      | ~ ( r2_hidden @ X27 @ ( k1_relat_1 @ X26 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t18_relat_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 ) @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('24',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','24'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('26',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('27',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['14','27'])).

thf('29',plain,(
    $false ),
    inference(simplify,[status(thm)],['28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bc1HP6Z1ev
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:17:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.19/0.43  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.43  % Solved by: fo/fo7.sh
% 0.19/0.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.43  % done 38 iterations in 0.013s
% 0.19/0.43  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.43  % SZS output start Refutation
% 0.19/0.43  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.43  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.43  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.43  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.43  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.43  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.43  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.19/0.43  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.19/0.43  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.43  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.43  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.43  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.43  thf(t60_relat_1, conjecture,
% 0.19/0.43    (( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.19/0.43     ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.19/0.43  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.43    (~( ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.19/0.43        ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) )),
% 0.19/0.43    inference('cnf.neg', [status(esa)], [t60_relat_1])).
% 0.19/0.43  thf('0', plain,
% 0.19/0.43      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.19/0.43        | ((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))),
% 0.19/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.43  thf('1', plain,
% 0.19/0.43      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.19/0.43         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.19/0.43      inference('split', [status(esa)], ['0'])).
% 0.19/0.43  thf(d5_relat_1, axiom,
% 0.19/0.43    (![A:$i,B:$i]:
% 0.19/0.43     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.19/0.43       ( ![C:$i]:
% 0.19/0.43         ( ( r2_hidden @ C @ B ) <=>
% 0.19/0.43           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.19/0.43  thf('2', plain,
% 0.19/0.43      (![X21 : $i, X24 : $i]:
% 0.19/0.43         (((X24) = (k2_relat_1 @ X21))
% 0.19/0.43          | (r2_hidden @ 
% 0.19/0.43             (k4_tarski @ (sk_D @ X24 @ X21) @ (sk_C @ X24 @ X21)) @ X21)
% 0.19/0.43          | (r2_hidden @ (sk_C @ X24 @ X21) @ X24))),
% 0.19/0.43      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.19/0.43  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.19/0.43  thf('3', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.19/0.43      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.19/0.43  thf(l24_zfmisc_1, axiom,
% 0.19/0.43    (![A:$i,B:$i]:
% 0.19/0.43     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.19/0.43  thf('4', plain,
% 0.19/0.43      (![X16 : $i, X17 : $i]:
% 0.19/0.43         (~ (r1_xboole_0 @ (k1_tarski @ X16) @ X17) | ~ (r2_hidden @ X16 @ X17))),
% 0.19/0.43      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.19/0.43  thf('5', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.19/0.43      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.43  thf('6', plain,
% 0.19/0.43      (![X0 : $i]:
% 0.19/0.43         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.19/0.43          | ((X0) = (k2_relat_1 @ k1_xboole_0)))),
% 0.19/0.43      inference('sup-', [status(thm)], ['2', '5'])).
% 0.19/0.43  thf('7', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.19/0.43      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.43  thf('8', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 0.19/0.43      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.43  thf('9', plain,
% 0.19/0.43      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.19/0.43         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.19/0.43      inference('split', [status(esa)], ['0'])).
% 0.19/0.43  thf('10', plain,
% 0.19/0.43      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.19/0.43         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.19/0.43      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.43  thf('11', plain, ((((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.19/0.43      inference('simplify', [status(thm)], ['10'])).
% 0.19/0.43  thf('12', plain,
% 0.19/0.43      (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.19/0.43       ~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.19/0.43      inference('split', [status(esa)], ['0'])).
% 0.19/0.43  thf('13', plain, (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.19/0.43      inference('sat_resolution*', [status(thm)], ['11', '12'])).
% 0.19/0.43  thf('14', plain, (((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.19/0.43      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.19/0.43  thf(cc1_relat_1, axiom,
% 0.19/0.43    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.19/0.43  thf('15', plain, (![X18 : $i]: ((v1_relat_1 @ X18) | ~ (v1_xboole_0 @ X18))),
% 0.19/0.43      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.19/0.43  thf('16', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 0.19/0.43      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.43  thf('17', plain,
% 0.19/0.43      (![X0 : $i]:
% 0.19/0.43         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.19/0.43          | ((X0) = (k2_relat_1 @ k1_xboole_0)))),
% 0.19/0.43      inference('sup-', [status(thm)], ['2', '5'])).
% 0.19/0.43  thf('18', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 0.19/0.43      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.43  thf('19', plain,
% 0.19/0.43      (![X0 : $i]:
% 0.19/0.43         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0) | ((X0) = (k1_xboole_0)))),
% 0.19/0.43      inference('demod', [status(thm)], ['17', '18'])).
% 0.19/0.43  thf(t18_relat_1, axiom,
% 0.19/0.43    (![A:$i,B:$i]:
% 0.19/0.43     ( ( v1_relat_1 @ B ) =>
% 0.19/0.43       ( ~( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) & 
% 0.19/0.43            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.19/0.43  thf('20', plain,
% 0.19/0.43      (![X26 : $i, X27 : $i]:
% 0.19/0.43         ((r2_hidden @ (sk_C_1 @ X26) @ (k2_relat_1 @ X26))
% 0.19/0.43          | ~ (r2_hidden @ X27 @ (k1_relat_1 @ X26))
% 0.19/0.43          | ~ (v1_relat_1 @ X26))),
% 0.19/0.43      inference('cnf', [status(esa)], [t18_relat_1])).
% 0.19/0.43  thf('21', plain,
% 0.19/0.43      (![X0 : $i]:
% 0.19/0.43         (((k1_relat_1 @ X0) = (k1_xboole_0))
% 0.19/0.43          | ~ (v1_relat_1 @ X0)
% 0.19/0.43          | (r2_hidden @ (sk_C_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.19/0.43      inference('sup-', [status(thm)], ['19', '20'])).
% 0.19/0.43  thf('22', plain,
% 0.19/0.43      (((r2_hidden @ (sk_C_1 @ k1_xboole_0) @ k1_xboole_0)
% 0.19/0.43        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.19/0.43        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.19/0.43      inference('sup+', [status(thm)], ['16', '21'])).
% 0.19/0.43  thf('23', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.19/0.43      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.43  thf('24', plain,
% 0.19/0.43      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.19/0.43        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.19/0.43      inference('clc', [status(thm)], ['22', '23'])).
% 0.19/0.43  thf('25', plain,
% 0.19/0.43      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.19/0.43        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.19/0.43      inference('sup-', [status(thm)], ['15', '24'])).
% 0.19/0.43  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.19/0.43  thf('26', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.43      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.43  thf('27', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.43      inference('demod', [status(thm)], ['25', '26'])).
% 0.19/0.43  thf('28', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.19/0.43      inference('demod', [status(thm)], ['14', '27'])).
% 0.19/0.43  thf('29', plain, ($false), inference('simplify', [status(thm)], ['28'])).
% 0.19/0.43  
% 0.19/0.43  % SZS output end Refutation
% 0.19/0.43  
% 0.19/0.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
