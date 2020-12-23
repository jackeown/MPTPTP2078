%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.N1zTy2zMuX

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:16 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :   51 (  61 expanded)
%              Number of leaves         :   21 (  27 expanded)
%              Depth                    :   14
%              Number of atoms          :  259 ( 364 expanded)
%              Number of equality atoms :   15 (  16 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t218_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v5_relat_1 @ C @ A ) )
         => ( v5_relat_1 @ C @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ A @ B )
       => ! [C: $i] :
            ( ( ( v1_relat_1 @ C )
              & ( v5_relat_1 @ C @ A ) )
           => ( v5_relat_1 @ C @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t218_relat_1])).

thf('0',plain,(
    ~ ( v5_relat_1 @ sk_C_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v5_relat_1 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v5_relat_1 @ X19 @ X20 )
      | ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('3',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['3','4'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X8: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X8 @ X10 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('7',plain,
    ( ( k4_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t34_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ) )).

thf('9',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ ( k4_xboole_0 @ X13 @ X12 ) @ ( k4_xboole_0 @ X13 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_B_1 ) @ ( k4_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['7','10'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('12',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r2_xboole_0 @ X3 @ X5 )
      | ( X3 = X5 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('13',plain,
    ( ( ( k4_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 )
      = k1_xboole_0 )
    | ( r2_xboole_0 @ ( k4_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ~ ( r2_hidden @ C @ A ) ) ) )).

thf('14',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('15',plain,
    ( ( ( k4_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ ( k4_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('16',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X14 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('17',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ( ( k4_xboole_0 @ X17 @ ( k1_tarski @ X16 ) )
       != X17 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( k4_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['15','19'])).

thf('21',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( ( k4_xboole_0 @ X8 @ X9 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('22',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ( v5_relat_1 @ X19 @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( v5_relat_1 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    $false ),
    inference(demod,[status(thm)],['0','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.N1zTy2zMuX
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:51:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.49/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.49/0.68  % Solved by: fo/fo7.sh
% 0.49/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.68  % done 348 iterations in 0.228s
% 0.49/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.49/0.68  % SZS output start Refutation
% 0.49/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.68  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.49/0.68  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.49/0.68  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.49/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.49/0.68  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.49/0.68  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.49/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.49/0.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.49/0.68  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.49/0.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.49/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.49/0.68  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.49/0.68  thf(t218_relat_1, conjecture,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( r1_tarski @ A @ B ) =>
% 0.49/0.68       ( ![C:$i]:
% 0.49/0.68         ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) ) =>
% 0.49/0.68           ( v5_relat_1 @ C @ B ) ) ) ))).
% 0.49/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.68    (~( ![A:$i,B:$i]:
% 0.49/0.68        ( ( r1_tarski @ A @ B ) =>
% 0.49/0.68          ( ![C:$i]:
% 0.49/0.68            ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) ) =>
% 0.49/0.68              ( v5_relat_1 @ C @ B ) ) ) ) )),
% 0.49/0.68    inference('cnf.neg', [status(esa)], [t218_relat_1])).
% 0.49/0.68  thf('0', plain, (~ (v5_relat_1 @ sk_C_1 @ sk_B_1)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('1', plain, ((v5_relat_1 @ sk_C_1 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf(d19_relat_1, axiom,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( v1_relat_1 @ B ) =>
% 0.49/0.68       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.49/0.68  thf('2', plain,
% 0.49/0.68      (![X19 : $i, X20 : $i]:
% 0.49/0.68         (~ (v5_relat_1 @ X19 @ X20)
% 0.49/0.68          | (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 0.49/0.68          | ~ (v1_relat_1 @ X19))),
% 0.49/0.68      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.49/0.68  thf('3', plain,
% 0.49/0.68      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_A))),
% 0.49/0.68      inference('sup-', [status(thm)], ['1', '2'])).
% 0.49/0.68  thf('4', plain, ((v1_relat_1 @ sk_C_1)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('5', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_A)),
% 0.49/0.68      inference('demod', [status(thm)], ['3', '4'])).
% 0.49/0.68  thf(l32_xboole_1, axiom,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.49/0.68  thf('6', plain,
% 0.49/0.68      (![X8 : $i, X10 : $i]:
% 0.49/0.68         (((k4_xboole_0 @ X8 @ X10) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ X10))),
% 0.49/0.68      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.49/0.68  thf('7', plain,
% 0.49/0.68      (((k4_xboole_0 @ (k2_relat_1 @ sk_C_1) @ sk_A) = (k1_xboole_0))),
% 0.49/0.68      inference('sup-', [status(thm)], ['5', '6'])).
% 0.49/0.68  thf('8', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf(t34_xboole_1, axiom,
% 0.49/0.68    (![A:$i,B:$i,C:$i]:
% 0.49/0.68     ( ( r1_tarski @ A @ B ) =>
% 0.49/0.68       ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ))).
% 0.49/0.68  thf('9', plain,
% 0.49/0.68      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.49/0.68         (~ (r1_tarski @ X11 @ X12)
% 0.49/0.68          | (r1_tarski @ (k4_xboole_0 @ X13 @ X12) @ (k4_xboole_0 @ X13 @ X11)))),
% 0.49/0.68      inference('cnf', [status(esa)], [t34_xboole_1])).
% 0.49/0.68  thf('10', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         (r1_tarski @ (k4_xboole_0 @ X0 @ sk_B_1) @ (k4_xboole_0 @ X0 @ sk_A))),
% 0.49/0.68      inference('sup-', [status(thm)], ['8', '9'])).
% 0.49/0.68  thf('11', plain,
% 0.49/0.68      ((r1_tarski @ (k4_xboole_0 @ (k2_relat_1 @ sk_C_1) @ sk_B_1) @ 
% 0.49/0.68        k1_xboole_0)),
% 0.49/0.68      inference('sup+', [status(thm)], ['7', '10'])).
% 0.49/0.68  thf(d8_xboole_0, axiom,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.49/0.68       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.49/0.68  thf('12', plain,
% 0.49/0.68      (![X3 : $i, X5 : $i]:
% 0.49/0.68         ((r2_xboole_0 @ X3 @ X5) | ((X3) = (X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.49/0.68      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.49/0.68  thf('13', plain,
% 0.49/0.68      ((((k4_xboole_0 @ (k2_relat_1 @ sk_C_1) @ sk_B_1) = (k1_xboole_0))
% 0.49/0.68        | (r2_xboole_0 @ (k4_xboole_0 @ (k2_relat_1 @ sk_C_1) @ sk_B_1) @ 
% 0.49/0.68           k1_xboole_0))),
% 0.49/0.68      inference('sup-', [status(thm)], ['11', '12'])).
% 0.49/0.68  thf(t6_xboole_0, axiom,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ~( ( r2_xboole_0 @ A @ B ) & 
% 0.49/0.68          ( ![C:$i]:
% 0.49/0.68            ( ~( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ) ) ) ))).
% 0.49/0.68  thf('14', plain,
% 0.49/0.68      (![X6 : $i, X7 : $i]:
% 0.49/0.68         (~ (r2_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.49/0.68      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.49/0.68  thf('15', plain,
% 0.49/0.68      ((((k4_xboole_0 @ (k2_relat_1 @ sk_C_1) @ sk_B_1) = (k1_xboole_0))
% 0.49/0.68        | (r2_hidden @ 
% 0.49/0.68           (sk_C @ k1_xboole_0 @ (k4_xboole_0 @ (k2_relat_1 @ sk_C_1) @ sk_B_1)) @ 
% 0.49/0.68           k1_xboole_0))),
% 0.49/0.68      inference('sup-', [status(thm)], ['13', '14'])).
% 0.49/0.68  thf(t4_boole, axiom,
% 0.49/0.68    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.49/0.68  thf('16', plain,
% 0.49/0.68      (![X14 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X14) = (k1_xboole_0))),
% 0.49/0.68      inference('cnf', [status(esa)], [t4_boole])).
% 0.49/0.68  thf(t65_zfmisc_1, axiom,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.49/0.68       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.49/0.68  thf('17', plain,
% 0.49/0.68      (![X16 : $i, X17 : $i]:
% 0.49/0.68         (~ (r2_hidden @ X16 @ X17)
% 0.49/0.68          | ((k4_xboole_0 @ X17 @ (k1_tarski @ X16)) != (X17)))),
% 0.49/0.68      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.49/0.68  thf('18', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         (((k1_xboole_0) != (k1_xboole_0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.49/0.68      inference('sup-', [status(thm)], ['16', '17'])).
% 0.49/0.68  thf('19', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.49/0.68      inference('simplify', [status(thm)], ['18'])).
% 0.49/0.68  thf('20', plain,
% 0.49/0.68      (((k4_xboole_0 @ (k2_relat_1 @ sk_C_1) @ sk_B_1) = (k1_xboole_0))),
% 0.49/0.68      inference('clc', [status(thm)], ['15', '19'])).
% 0.49/0.68  thf('21', plain,
% 0.49/0.68      (![X8 : $i, X9 : $i]:
% 0.49/0.68         ((r1_tarski @ X8 @ X9) | ((k4_xboole_0 @ X8 @ X9) != (k1_xboole_0)))),
% 0.49/0.68      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.49/0.68  thf('22', plain,
% 0.49/0.68      ((((k1_xboole_0) != (k1_xboole_0))
% 0.49/0.68        | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))),
% 0.49/0.68      inference('sup-', [status(thm)], ['20', '21'])).
% 0.49/0.68  thf('23', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)),
% 0.49/0.68      inference('simplify', [status(thm)], ['22'])).
% 0.49/0.68  thf('24', plain,
% 0.49/0.68      (![X19 : $i, X20 : $i]:
% 0.49/0.68         (~ (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 0.49/0.68          | (v5_relat_1 @ X19 @ X20)
% 0.49/0.68          | ~ (v1_relat_1 @ X19))),
% 0.49/0.68      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.49/0.68  thf('25', plain,
% 0.49/0.68      ((~ (v1_relat_1 @ sk_C_1) | (v5_relat_1 @ sk_C_1 @ sk_B_1))),
% 0.49/0.68      inference('sup-', [status(thm)], ['23', '24'])).
% 0.49/0.68  thf('26', plain, ((v1_relat_1 @ sk_C_1)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('27', plain, ((v5_relat_1 @ sk_C_1 @ sk_B_1)),
% 0.49/0.68      inference('demod', [status(thm)], ['25', '26'])).
% 0.49/0.68  thf('28', plain, ($false), inference('demod', [status(thm)], ['0', '27'])).
% 0.49/0.68  
% 0.49/0.68  % SZS output end Refutation
% 0.49/0.68  
% 0.49/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
