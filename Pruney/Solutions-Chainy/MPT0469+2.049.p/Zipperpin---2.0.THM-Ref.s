%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3CK5jsNPJZ

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   51 (  66 expanded)
%              Number of leaves         :   17 (  28 expanded)
%              Depth                    :   13
%              Number of atoms          :  257 ( 335 expanded)
%              Number of equality atoms :   37 (  52 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('0',plain,(
    ! [X13: $i,X16: $i] :
      ( ( X16
        = ( k2_relat_1 @ X13 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X16 @ X13 ) @ ( sk_C_1 @ X16 @ X13 ) ) @ X13 )
      | ( r2_hidden @ ( sk_C_1 @ X16 @ X13 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X0
        = ( k2_relat_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

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

thf('5',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('7',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('8',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('9',plain,
    ( ( ( k2_relat_1 @ o_0_0_xboole_0 )
     != o_0_0_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('10',plain,(
    ! [X6: $i,X9: $i] :
      ( ( X9
        = ( k1_relat_1 @ X6 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X9 @ X6 ) @ ( sk_D @ X9 @ X6 ) ) @ X6 )
      | ( r2_hidden @ ( sk_C @ X9 @ X6 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X0
        = ( k1_relat_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf('16',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('18',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('19',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ( X0 != o_0_0_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17','18','19'])).

thf('21',plain,
    ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('23',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('simplify_reflect+',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf('25',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['23','24'])).

thf('26',plain,(
    ( k2_relat_1 @ o_0_0_xboole_0 )
 != o_0_0_xboole_0 ),
    inference(simpl_trail,[status(thm)],['9','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( X0 != o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','26'])).

thf('28',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( X0 != o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( v1_xboole_0 @ o_0_0_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('32',plain,(
    $false ),
    inference('simplify_reflect+',[status(thm)],['30','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3CK5jsNPJZ
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:38:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 37 iterations in 0.024s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.48  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.22/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.48  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.22/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.48  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 0.22/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.48  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.22/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.48  thf(d5_relat_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.22/0.48       ( ![C:$i]:
% 0.22/0.48         ( ( r2_hidden @ C @ B ) <=>
% 0.22/0.48           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.22/0.48  thf('0', plain,
% 0.22/0.48      (![X13 : $i, X16 : $i]:
% 0.22/0.48         (((X16) = (k2_relat_1 @ X13))
% 0.22/0.48          | (r2_hidden @ 
% 0.22/0.48             (k4_tarski @ (sk_D_2 @ X16 @ X13) @ (sk_C_1 @ X16 @ X13)) @ X13)
% 0.22/0.48          | (r2_hidden @ (sk_C_1 @ X16 @ X13) @ X16))),
% 0.22/0.48      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.22/0.48  thf(d1_xboole_0, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.48  thf('1', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.22/0.48      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.48  thf('2', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 0.22/0.48          | ((X1) = (k2_relat_1 @ X0))
% 0.22/0.48          | ~ (v1_xboole_0 @ X0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.48  thf('3', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.22/0.48      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.48  thf('4', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         (~ (v1_xboole_0 @ X1)
% 0.22/0.48          | ((X0) = (k2_relat_1 @ X1))
% 0.22/0.48          | ~ (v1_xboole_0 @ X0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.48  thf(t60_relat_1, conjecture,
% 0.22/0.48    (( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.22/0.48     ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.22/0.48        ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t60_relat_1])).
% 0.22/0.48  thf('5', plain,
% 0.22/0.48      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.22/0.48        | ((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('6', plain,
% 0.22/0.48      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.22/0.48         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.22/0.48      inference('split', [status(esa)], ['5'])).
% 0.22/0.48  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.22/0.48  thf('7', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.22/0.48      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.22/0.48  thf('8', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.22/0.48      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.22/0.48  thf('9', plain,
% 0.22/0.48      ((((k2_relat_1 @ o_0_0_xboole_0) != (o_0_0_xboole_0)))
% 0.22/0.48         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.22/0.48      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.22/0.48  thf(d4_relat_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.22/0.48       ( ![C:$i]:
% 0.22/0.48         ( ( r2_hidden @ C @ B ) <=>
% 0.22/0.48           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.22/0.48  thf('10', plain,
% 0.22/0.48      (![X6 : $i, X9 : $i]:
% 0.22/0.48         (((X9) = (k1_relat_1 @ X6))
% 0.22/0.48          | (r2_hidden @ (k4_tarski @ (sk_C @ X9 @ X6) @ (sk_D @ X9 @ X6)) @ X6)
% 0.22/0.48          | (r2_hidden @ (sk_C @ X9 @ X6) @ X9))),
% 0.22/0.48      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.22/0.48  thf('11', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.22/0.48      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.48  thf('12', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 0.22/0.48          | ((X1) = (k1_relat_1 @ X0))
% 0.22/0.48          | ~ (v1_xboole_0 @ X0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.48  thf('13', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.22/0.48      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.48  thf('14', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         (~ (v1_xboole_0 @ X1)
% 0.22/0.48          | ((X0) = (k1_relat_1 @ X1))
% 0.22/0.48          | ~ (v1_xboole_0 @ X0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.48  thf('15', plain,
% 0.22/0.48      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.22/0.48         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.22/0.48      inference('split', [status(esa)], ['5'])).
% 0.22/0.48  thf('16', plain,
% 0.22/0.48      ((![X0 : $i]:
% 0.22/0.48          (((X0) != (k1_xboole_0))
% 0.22/0.48           | ~ (v1_xboole_0 @ X0)
% 0.22/0.48           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.22/0.48         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.22/0.48      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.48  thf('17', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.22/0.48      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.22/0.48  thf('18', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.22/0.48      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.22/0.48  thf(dt_o_0_0_xboole_0, axiom, (v1_xboole_0 @ o_0_0_xboole_0)).
% 0.22/0.48  thf('19', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_o_0_0_xboole_0])).
% 0.22/0.48  thf('20', plain,
% 0.22/0.48      ((![X0 : $i]: (((X0) != (o_0_0_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.22/0.48         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.22/0.48      inference('demod', [status(thm)], ['16', '17', '18', '19'])).
% 0.22/0.48  thf('21', plain,
% 0.22/0.48      ((~ (v1_xboole_0 @ o_0_0_xboole_0))
% 0.22/0.48         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.22/0.48      inference('simplify', [status(thm)], ['20'])).
% 0.22/0.48  thf('22', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_o_0_0_xboole_0])).
% 0.22/0.48  thf('23', plain, ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.22/0.48      inference('simplify_reflect+', [status(thm)], ['21', '22'])).
% 0.22/0.48  thf('24', plain,
% 0.22/0.48      (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.22/0.48       ~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.22/0.48      inference('split', [status(esa)], ['5'])).
% 0.22/0.48  thf('25', plain, (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.22/0.48      inference('sat_resolution*', [status(thm)], ['23', '24'])).
% 0.22/0.48  thf('26', plain, (((k2_relat_1 @ o_0_0_xboole_0) != (o_0_0_xboole_0))),
% 0.22/0.48      inference('simpl_trail', [status(thm)], ['9', '25'])).
% 0.22/0.48  thf('27', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (((X0) != (o_0_0_xboole_0))
% 0.22/0.48          | ~ (v1_xboole_0 @ X0)
% 0.22/0.48          | ~ (v1_xboole_0 @ o_0_0_xboole_0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['4', '26'])).
% 0.22/0.48  thf('28', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_o_0_0_xboole_0])).
% 0.22/0.48  thf('29', plain,
% 0.22/0.48      (![X0 : $i]: (((X0) != (o_0_0_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.48      inference('demod', [status(thm)], ['27', '28'])).
% 0.22/0.48  thf('30', plain, (~ (v1_xboole_0 @ o_0_0_xboole_0)),
% 0.22/0.48      inference('simplify', [status(thm)], ['29'])).
% 0.22/0.48  thf('31', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_o_0_0_xboole_0])).
% 0.22/0.48  thf('32', plain, ($false),
% 0.22/0.48      inference('simplify_reflect+', [status(thm)], ['30', '31'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
