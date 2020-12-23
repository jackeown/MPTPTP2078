%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wREqNWY4MT

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:41 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   48 (  67 expanded)
%              Number of leaves         :   15 (  24 expanded)
%              Depth                    :   14
%              Number of atoms          :  339 ( 499 expanded)
%              Number of equality atoms :   40 (  58 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ B @ C ) )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X37: $i,X38: $i] :
      ( ( X37 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_2 @ X38 @ X37 ) @ X37 )
      | ( r1_tarski @ X38 @ ( k1_setfam_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('1',plain,(
    ! [X26: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X29 @ X28 )
      | ( X29 = X26 )
      | ( X28
       != ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('2',plain,(
    ! [X26: $i,X29: $i] :
      ( ( X29 = X26 )
      | ~ ( r2_hidden @ X29 @ ( k1_tarski @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_C_2 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( X10 != X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( X27 != X26 )
      | ( r2_hidden @ X27 @ X28 )
      | ( X28
       != ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('7',plain,(
    ! [X26: $i] :
      ( r2_hidden @ X26 @ ( k1_tarski @ X26 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t8_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ C ) ) )).

thf('8',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( r2_hidden @ X39 @ X40 )
      | ~ ( r1_tarski @ X39 @ X41 )
      | ( r1_tarski @ ( k1_setfam_1 @ X40 ) @ X41 ) ) ),
    inference(cnf,[status(esa)],[t8_setfam_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_2 @ X0 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','12'])).

thf('14',plain,(
    ! [X37: $i,X38: $i] :
      ( ( X37 = k1_xboole_0 )
      | ~ ( r1_tarski @ X38 @ ( sk_C_2 @ X38 @ X37 ) )
      | ( r1_tarski @ X38 @ ( k1_setfam_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf(t11_setfam_1,conjecture,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t11_setfam_1])).

thf('21',plain,(
    ( k1_setfam_1 @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( sk_A != sk_A )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X26: $i] :
      ( r2_hidden @ X26 @ ( k1_tarski @ X26 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('25',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('26',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('27',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('28',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['29'])).

thf('31',plain,(
    $false ),
    inference('sup-',[status(thm)],['25','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wREqNWY4MT
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:35:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.65  % Solved by: fo/fo7.sh
% 0.46/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.65  % done 251 iterations in 0.184s
% 0.46/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.65  % SZS output start Refutation
% 0.46/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.65  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.46/0.65  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.46/0.65  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.65  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.65  thf(t6_setfam_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ B @ C ) ) ) =>
% 0.46/0.65       ( ( ( A ) = ( k1_xboole_0 ) ) | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.46/0.65  thf('0', plain,
% 0.46/0.65      (![X37 : $i, X38 : $i]:
% 0.46/0.65         (((X37) = (k1_xboole_0))
% 0.46/0.65          | (r2_hidden @ (sk_C_2 @ X38 @ X37) @ X37)
% 0.46/0.65          | (r1_tarski @ X38 @ (k1_setfam_1 @ X37)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.46/0.65  thf(d1_tarski, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.46/0.65       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.46/0.65  thf('1', plain,
% 0.46/0.65      (![X26 : $i, X28 : $i, X29 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X29 @ X28)
% 0.46/0.65          | ((X29) = (X26))
% 0.46/0.65          | ((X28) != (k1_tarski @ X26)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d1_tarski])).
% 0.46/0.65  thf('2', plain,
% 0.46/0.65      (![X26 : $i, X29 : $i]:
% 0.46/0.65         (((X29) = (X26)) | ~ (r2_hidden @ X29 @ (k1_tarski @ X26)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['1'])).
% 0.46/0.65  thf('3', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((r1_tarski @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.46/0.65          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.46/0.65          | ((sk_C_2 @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['0', '2'])).
% 0.46/0.65  thf(d10_xboole_0, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.65  thf('4', plain,
% 0.46/0.65      (![X10 : $i, X11 : $i]: ((r1_tarski @ X10 @ X11) | ((X10) != (X11)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.65  thf('5', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 0.46/0.65      inference('simplify', [status(thm)], ['4'])).
% 0.46/0.65  thf('6', plain,
% 0.46/0.65      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.46/0.65         (((X27) != (X26))
% 0.46/0.65          | (r2_hidden @ X27 @ X28)
% 0.46/0.65          | ((X28) != (k1_tarski @ X26)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d1_tarski])).
% 0.46/0.65  thf('7', plain, (![X26 : $i]: (r2_hidden @ X26 @ (k1_tarski @ X26))),
% 0.46/0.65      inference('simplify', [status(thm)], ['6'])).
% 0.46/0.65  thf(t8_setfam_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( ( r2_hidden @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.46/0.65       ( r1_tarski @ ( k1_setfam_1 @ B ) @ C ) ))).
% 0.46/0.65  thf('8', plain,
% 0.46/0.65      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X39 @ X40)
% 0.46/0.65          | ~ (r1_tarski @ X39 @ X41)
% 0.46/0.65          | (r1_tarski @ (k1_setfam_1 @ X40) @ X41))),
% 0.46/0.65      inference('cnf', [status(esa)], [t8_setfam_1])).
% 0.46/0.65  thf('9', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((r1_tarski @ (k1_setfam_1 @ (k1_tarski @ X0)) @ X1)
% 0.46/0.65          | ~ (r1_tarski @ X0 @ X1))),
% 0.46/0.65      inference('sup-', [status(thm)], ['7', '8'])).
% 0.46/0.65  thf('10', plain,
% 0.46/0.65      (![X0 : $i]: (r1_tarski @ (k1_setfam_1 @ (k1_tarski @ X0)) @ X0)),
% 0.46/0.65      inference('sup-', [status(thm)], ['5', '9'])).
% 0.46/0.65  thf('11', plain,
% 0.46/0.65      (![X10 : $i, X12 : $i]:
% 0.46/0.65         (((X10) = (X12))
% 0.46/0.65          | ~ (r1_tarski @ X12 @ X10)
% 0.46/0.65          | ~ (r1_tarski @ X10 @ X12))),
% 0.46/0.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.65  thf('12', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.46/0.65          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.65  thf('13', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((sk_C_2 @ X0 @ (k1_tarski @ X0)) = (X0))
% 0.46/0.65          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.46/0.65          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['3', '12'])).
% 0.46/0.65  thf('14', plain,
% 0.46/0.65      (![X37 : $i, X38 : $i]:
% 0.46/0.65         (((X37) = (k1_xboole_0))
% 0.46/0.65          | ~ (r1_tarski @ X38 @ (sk_C_2 @ X38 @ X37))
% 0.46/0.65          | (r1_tarski @ X38 @ (k1_setfam_1 @ X37)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.46/0.65  thf('15', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (r1_tarski @ X0 @ X0)
% 0.46/0.65          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.46/0.65          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.46/0.65          | (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.46/0.65          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['13', '14'])).
% 0.46/0.65  thf('16', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 0.46/0.65      inference('simplify', [status(thm)], ['4'])).
% 0.46/0.65  thf('17', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.46/0.65          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.46/0.65          | (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.46/0.65          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.46/0.65      inference('demod', [status(thm)], ['15', '16'])).
% 0.46/0.65  thf('18', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.46/0.65          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.46/0.65          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.46/0.65      inference('simplify', [status(thm)], ['17'])).
% 0.46/0.65  thf('19', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.46/0.65          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.65  thf('20', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.46/0.65          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.46/0.65      inference('clc', [status(thm)], ['18', '19'])).
% 0.46/0.65  thf(t11_setfam_1, conjecture,
% 0.46/0.65    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.46/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.65    (~( ![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ) )),
% 0.46/0.65    inference('cnf.neg', [status(esa)], [t11_setfam_1])).
% 0.46/0.65  thf('21', plain, (((k1_setfam_1 @ (k1_tarski @ sk_A)) != (sk_A))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('22', plain,
% 0.46/0.65      ((((sk_A) != (sk_A)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['20', '21'])).
% 0.46/0.65  thf('23', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['22'])).
% 0.46/0.65  thf('24', plain, (![X26 : $i]: (r2_hidden @ X26 @ (k1_tarski @ X26))),
% 0.46/0.65      inference('simplify', [status(thm)], ['6'])).
% 0.46/0.65  thf('25', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.46/0.65      inference('sup+', [status(thm)], ['23', '24'])).
% 0.46/0.65  thf(t3_boole, axiom,
% 0.46/0.65    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.65  thf('26', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.46/0.65      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.65  thf(d5_xboole_0, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.46/0.65       ( ![D:$i]:
% 0.46/0.65         ( ( r2_hidden @ D @ C ) <=>
% 0.46/0.65           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.46/0.65  thf('27', plain,
% 0.46/0.65      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X8 @ X7)
% 0.46/0.65          | ~ (r2_hidden @ X8 @ X6)
% 0.46/0.65          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.46/0.65  thf('28', plain,
% 0.46/0.65      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X8 @ X6)
% 0.46/0.65          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['27'])).
% 0.46/0.65  thf('29', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['26', '28'])).
% 0.46/0.65  thf('30', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.46/0.65      inference('condensation', [status(thm)], ['29'])).
% 0.46/0.65  thf('31', plain, ($false), inference('sup-', [status(thm)], ['25', '30'])).
% 0.46/0.65  
% 0.46/0.65  % SZS output end Refutation
% 0.46/0.65  
% 0.46/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
