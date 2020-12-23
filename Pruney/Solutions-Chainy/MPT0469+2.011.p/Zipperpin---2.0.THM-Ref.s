%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.A7sZD8AaU5

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   59 (  74 expanded)
%              Number of leaves         :   20 (  31 expanded)
%              Depth                    :   12
%              Number of atoms          :  324 ( 419 expanded)
%              Number of equality atoms :   34 (  48 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('0',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X8 )
      | ( r2_hidden @ ( k4_tarski @ X9 @ ( sk_D_1 @ X9 @ X7 ) ) @ X7 )
      | ( X8
       != ( k1_relat_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('3',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X9 @ ( sk_D_1 @ X9 @ X7 ) ) @ X7 )
      | ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_relat_1 @ X0 ) ) @ ( sk_D_1 @ ( sk_B @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('7',plain,(
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

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X12 ) @ ( k1_relat_1 @ X12 ) )
      | ~ ( r2_hidden @ X13 @ ( k2_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t19_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

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

thf('16',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,
    ( ! [X0: $i] :
        ( ( ( k2_relat_1 @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X7: $i,X10: $i] :
      ( ( X10
        = ( k1_relat_1 @ X7 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X10 @ X7 ) @ ( sk_D @ X10 @ X7 ) ) @ X7 )
      | ( r2_hidden @ ( sk_C @ X10 @ X7 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X0
        = ( k1_relat_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('25',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('30',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('simplify_reflect+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('32',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['18','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['12','33'])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('35',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('36',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ X0 ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.A7sZD8AaU5
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:43:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 91 iterations in 0.063s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.52  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.52  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.21/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.52  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.21/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.52  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.52  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.52  thf(d1_xboole_0, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.52  thf(d4_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.21/0.52       ( ![C:$i]:
% 0.21/0.52         ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.52           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X9 @ X8)
% 0.21/0.52          | (r2_hidden @ (k4_tarski @ X9 @ (sk_D_1 @ X9 @ X7)) @ X7)
% 0.21/0.52          | ((X8) != (k1_relat_1 @ X7)))),
% 0.21/0.52      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X7 : $i, X9 : $i]:
% 0.21/0.52         ((r2_hidden @ (k4_tarski @ X9 @ (sk_D_1 @ X9 @ X7)) @ X7)
% 0.21/0.52          | ~ (r2_hidden @ X9 @ (k1_relat_1 @ X7)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.21/0.52          | (r2_hidden @ 
% 0.21/0.52             (k4_tarski @ (sk_B @ (k1_relat_1 @ X0)) @ 
% 0.21/0.52              (sk_D_1 @ (sk_B @ (k1_relat_1 @ X0)) @ X0)) @ 
% 0.21/0.52             X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['1', '3'])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (![X0 : $i]: ((v1_xboole_0 @ (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.52  thf(t7_xboole_0, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.52          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X3 : $i]: (((X3) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X3) @ X3))),
% 0.21/0.52      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.52  thf(t19_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ B ) =>
% 0.21/0.52       ( ~( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) & 
% 0.21/0.52            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X12 : $i, X13 : $i]:
% 0.21/0.52         ((r2_hidden @ (sk_C_1 @ X12) @ (k1_relat_1 @ X12))
% 0.21/0.52          | ~ (r2_hidden @ X13 @ (k2_relat_1 @ X12))
% 0.21/0.52          | ~ (v1_relat_1 @ X12))),
% 0.21/0.52      inference('cnf', [status(esa)], [t19_relat_1])).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.21/0.52          | ~ (v1_relat_1 @ X0)
% 0.21/0.52          | (r2_hidden @ (sk_C_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X0)
% 0.21/0.52          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.21/0.52          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (v1_xboole_0 @ X0)
% 0.21/0.52          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.21/0.52          | ~ (v1_relat_1 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['6', '11'])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X3 : $i]: (((X3) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X3) @ X3))),
% 0.21/0.52      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.52  thf(t60_relat_1, conjecture,
% 0.21/0.52    (( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.52     ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.52        ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t60_relat_1])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.21/0.52        | ((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.52         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.52      inference('split', [status(esa)], ['16'])).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      ((![X0 : $i]:
% 0.21/0.52          (((k2_relat_1 @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.21/0.52         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['15', '17'])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (![X7 : $i, X10 : $i]:
% 0.21/0.52         (((X10) = (k1_relat_1 @ X7))
% 0.21/0.52          | (r2_hidden @ (k4_tarski @ (sk_C @ X10 @ X7) @ (sk_D @ X10 @ X7)) @ 
% 0.21/0.52             X7)
% 0.21/0.52          | (r2_hidden @ (sk_C @ X10 @ X7) @ X10))),
% 0.21/0.52      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 0.21/0.52          | ((X1) = (k1_relat_1 @ X0))
% 0.21/0.52          | ~ (v1_xboole_0 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (v1_xboole_0 @ X1)
% 0.21/0.52          | ((X0) = (k1_relat_1 @ X1))
% 0.21/0.52          | ~ (v1_xboole_0 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.52         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.52      inference('split', [status(esa)], ['16'])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      ((![X0 : $i]:
% 0.21/0.52          (((X0) != (k1_xboole_0))
% 0.21/0.52           | ~ (v1_xboole_0 @ X0)
% 0.21/0.52           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.21/0.52         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.52  thf('26', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      ((![X0 : $i]: (((X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.21/0.52         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.52      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.21/0.52         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.52      inference('simplify', [status(thm)], ['27'])).
% 0.21/0.52  thf('29', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.52  thf('30', plain, ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.52      inference('simplify_reflect+', [status(thm)], ['28', '29'])).
% 0.21/0.52  thf('31', plain,
% 0.21/0.52      (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.21/0.52       ~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.52      inference('split', [status(esa)], ['16'])).
% 0.21/0.52  thf('32', plain, (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.52      inference('sat_resolution*', [status(thm)], ['30', '31'])).
% 0.21/0.52  thf('33', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k2_relat_1 @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.52      inference('simpl_trail', [status(thm)], ['18', '32'])).
% 0.21/0.52  thf('34', plain, (![X0 : $i]: (~ (v1_relat_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.52      inference('clc', [status(thm)], ['12', '33'])).
% 0.21/0.52  thf(cc1_relat_1, axiom,
% 0.21/0.52    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.21/0.52  thf('35', plain, (![X4 : $i]: ((v1_relat_1 @ X4) | ~ (v1_xboole_0 @ X4))),
% 0.21/0.52      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.21/0.52  thf('36', plain, (![X0 : $i]: ~ (v1_xboole_0 @ X0)),
% 0.21/0.52      inference('clc', [status(thm)], ['34', '35'])).
% 0.21/0.52  thf('37', plain, ($false), inference('sup-', [status(thm)], ['0', '36'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
