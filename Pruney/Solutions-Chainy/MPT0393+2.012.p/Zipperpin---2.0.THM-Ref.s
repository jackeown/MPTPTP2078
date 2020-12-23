%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.75nX2VRb4n

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:42 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   48 (  67 expanded)
%              Number of leaves         :   15 (  24 expanded)
%              Depth                    :   14
%              Number of atoms          :  339 ( 499 expanded)
%              Number of equality atoms :   40 (  58 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X42: $i,X43: $i] :
      ( ( X42 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_3 @ X43 @ X42 ) @ X42 )
      | ( r1_tarski @ X43 @ ( k1_setfam_1 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('1',plain,(
    ! [X24: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X27 @ X26 )
      | ( X27 = X24 )
      | ( X26
       != ( k1_tarski @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('2',plain,(
    ! [X24: $i,X27: $i] :
      ( ( X27 = X24 )
      | ~ ( r2_hidden @ X27 @ ( k1_tarski @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_C_3 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( X25 != X24 )
      | ( r2_hidden @ X25 @ X26 )
      | ( X26
       != ( k1_tarski @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('7',plain,(
    ! [X24: $i] :
      ( r2_hidden @ X24 @ ( k1_tarski @ X24 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t8_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ C ) ) )).

thf('8',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( r2_hidden @ X44 @ X45 )
      | ~ ( r1_tarski @ X44 @ X46 )
      | ( r1_tarski @ ( k1_setfam_1 @ X45 ) @ X46 ) ) ),
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
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_3 @ X0 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','12'])).

thf('14',plain,(
    ! [X42: $i,X43: $i] :
      ( ( X42 = k1_xboole_0 )
      | ~ ( r1_tarski @ X43 @ ( sk_C_3 @ X43 @ X42 ) )
      | ( r1_tarski @ X43 @ ( k1_setfam_1 @ X42 ) ) ) ),
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
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
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
    ! [X24: $i] :
      ( r2_hidden @ X24 @ ( k1_tarski @ X24 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('25',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('26',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
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
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('28',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.75nX2VRb4n
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:19:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.75/0.95  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.75/0.95  % Solved by: fo/fo7.sh
% 0.75/0.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.95  % done 665 iterations in 0.505s
% 0.75/0.95  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.75/0.95  % SZS output start Refutation
% 0.75/0.95  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.75/0.95  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.75/0.95  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.75/0.95  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.75/0.95  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 0.75/0.95  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/0.95  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.95  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.75/0.95  thf(t6_setfam_1, axiom,
% 0.75/0.95    (![A:$i,B:$i]:
% 0.75/0.95     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ B @ C ) ) ) =>
% 0.75/0.95       ( ( ( A ) = ( k1_xboole_0 ) ) | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.75/0.95  thf('0', plain,
% 0.75/0.95      (![X42 : $i, X43 : $i]:
% 0.75/0.95         (((X42) = (k1_xboole_0))
% 0.75/0.95          | (r2_hidden @ (sk_C_3 @ X43 @ X42) @ X42)
% 0.75/0.95          | (r1_tarski @ X43 @ (k1_setfam_1 @ X42)))),
% 0.75/0.95      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.75/0.95  thf(d1_tarski, axiom,
% 0.75/0.95    (![A:$i,B:$i]:
% 0.75/0.95     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.75/0.95       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.75/0.95  thf('1', plain,
% 0.75/0.95      (![X24 : $i, X26 : $i, X27 : $i]:
% 0.75/0.95         (~ (r2_hidden @ X27 @ X26)
% 0.75/0.95          | ((X27) = (X24))
% 0.75/0.95          | ((X26) != (k1_tarski @ X24)))),
% 0.75/0.95      inference('cnf', [status(esa)], [d1_tarski])).
% 0.75/0.95  thf('2', plain,
% 0.75/0.95      (![X24 : $i, X27 : $i]:
% 0.75/0.95         (((X27) = (X24)) | ~ (r2_hidden @ X27 @ (k1_tarski @ X24)))),
% 0.75/0.95      inference('simplify', [status(thm)], ['1'])).
% 0.75/0.95  thf('3', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         ((r1_tarski @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.75/0.95          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.75/0.95          | ((sk_C_3 @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['0', '2'])).
% 0.75/0.95  thf(d10_xboole_0, axiom,
% 0.75/0.95    (![A:$i,B:$i]:
% 0.75/0.95     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.75/0.95  thf('4', plain,
% 0.75/0.95      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 0.75/0.95      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.75/0.95  thf('5', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 0.75/0.95      inference('simplify', [status(thm)], ['4'])).
% 0.75/0.95  thf('6', plain,
% 0.75/0.95      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.75/0.95         (((X25) != (X24))
% 0.75/0.95          | (r2_hidden @ X25 @ X26)
% 0.75/0.95          | ((X26) != (k1_tarski @ X24)))),
% 0.75/0.95      inference('cnf', [status(esa)], [d1_tarski])).
% 0.75/0.95  thf('7', plain, (![X24 : $i]: (r2_hidden @ X24 @ (k1_tarski @ X24))),
% 0.75/0.95      inference('simplify', [status(thm)], ['6'])).
% 0.75/0.95  thf(t8_setfam_1, axiom,
% 0.75/0.95    (![A:$i,B:$i,C:$i]:
% 0.75/0.95     ( ( ( r2_hidden @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.75/0.95       ( r1_tarski @ ( k1_setfam_1 @ B ) @ C ) ))).
% 0.75/0.95  thf('8', plain,
% 0.75/0.95      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.75/0.95         (~ (r2_hidden @ X44 @ X45)
% 0.75/0.95          | ~ (r1_tarski @ X44 @ X46)
% 0.75/0.95          | (r1_tarski @ (k1_setfam_1 @ X45) @ X46))),
% 0.75/0.95      inference('cnf', [status(esa)], [t8_setfam_1])).
% 0.75/0.95  thf('9', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         ((r1_tarski @ (k1_setfam_1 @ (k1_tarski @ X0)) @ X1)
% 0.75/0.95          | ~ (r1_tarski @ X0 @ X1))),
% 0.75/0.95      inference('sup-', [status(thm)], ['7', '8'])).
% 0.75/0.95  thf('10', plain,
% 0.75/0.95      (![X0 : $i]: (r1_tarski @ (k1_setfam_1 @ (k1_tarski @ X0)) @ X0)),
% 0.75/0.95      inference('sup-', [status(thm)], ['5', '9'])).
% 0.75/0.95  thf('11', plain,
% 0.75/0.95      (![X8 : $i, X10 : $i]:
% 0.75/0.95         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.75/0.95      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.75/0.95  thf('12', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.75/0.95          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.75/0.95      inference('sup-', [status(thm)], ['10', '11'])).
% 0.75/0.95  thf('13', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         (((sk_C_3 @ X0 @ (k1_tarski @ X0)) = (X0))
% 0.75/0.95          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.75/0.95          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.75/0.95      inference('sup-', [status(thm)], ['3', '12'])).
% 0.75/0.95  thf('14', plain,
% 0.75/0.95      (![X42 : $i, X43 : $i]:
% 0.75/0.95         (((X42) = (k1_xboole_0))
% 0.75/0.95          | ~ (r1_tarski @ X43 @ (sk_C_3 @ X43 @ X42))
% 0.75/0.95          | (r1_tarski @ X43 @ (k1_setfam_1 @ X42)))),
% 0.75/0.95      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.75/0.95  thf('15', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         (~ (r1_tarski @ X0 @ X0)
% 0.75/0.95          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.75/0.95          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.75/0.95          | (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.75/0.95          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['13', '14'])).
% 0.75/0.95  thf('16', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 0.75/0.95      inference('simplify', [status(thm)], ['4'])).
% 0.75/0.95  thf('17', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.75/0.95          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.75/0.95          | (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.75/0.95          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.75/0.95      inference('demod', [status(thm)], ['15', '16'])).
% 0.75/0.95  thf('18', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         ((r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.75/0.95          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.75/0.95          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.75/0.95      inference('simplify', [status(thm)], ['17'])).
% 0.75/0.95  thf('19', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.75/0.95          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.75/0.95      inference('sup-', [status(thm)], ['10', '11'])).
% 0.75/0.95  thf('20', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.75/0.95          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.75/0.95      inference('clc', [status(thm)], ['18', '19'])).
% 0.75/0.95  thf(t11_setfam_1, conjecture,
% 0.75/0.95    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.75/0.95  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.95    (~( ![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ) )),
% 0.75/0.95    inference('cnf.neg', [status(esa)], [t11_setfam_1])).
% 0.75/0.95  thf('21', plain, (((k1_setfam_1 @ (k1_tarski @ sk_A)) != (sk_A))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('22', plain,
% 0.75/0.95      ((((sk_A) != (sk_A)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['20', '21'])).
% 0.75/0.95  thf('23', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.75/0.95      inference('simplify', [status(thm)], ['22'])).
% 0.75/0.95  thf('24', plain, (![X24 : $i]: (r2_hidden @ X24 @ (k1_tarski @ X24))),
% 0.75/0.95      inference('simplify', [status(thm)], ['6'])).
% 0.75/0.95  thf('25', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.75/0.95      inference('sup+', [status(thm)], ['23', '24'])).
% 0.75/0.95  thf(t3_boole, axiom,
% 0.75/0.95    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.75/0.95  thf('26', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.75/0.95      inference('cnf', [status(esa)], [t3_boole])).
% 0.75/0.95  thf(d5_xboole_0, axiom,
% 0.75/0.95    (![A:$i,B:$i,C:$i]:
% 0.75/0.95     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.75/0.95       ( ![D:$i]:
% 0.75/0.95         ( ( r2_hidden @ D @ C ) <=>
% 0.75/0.95           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.75/0.95  thf('27', plain,
% 0.75/0.95      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.75/0.95         (~ (r2_hidden @ X4 @ X3)
% 0.75/0.95          | ~ (r2_hidden @ X4 @ X2)
% 0.75/0.95          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.75/0.95      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.75/0.95  thf('28', plain,
% 0.75/0.95      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.75/0.95         (~ (r2_hidden @ X4 @ X2)
% 0.75/0.95          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.75/0.95      inference('simplify', [status(thm)], ['27'])).
% 0.75/0.95  thf('29', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.75/0.95      inference('sup-', [status(thm)], ['26', '28'])).
% 0.75/0.95  thf('30', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.75/0.95      inference('condensation', [status(thm)], ['29'])).
% 0.75/0.95  thf('31', plain, ($false), inference('sup-', [status(thm)], ['25', '30'])).
% 0.75/0.95  
% 0.75/0.95  % SZS output end Refutation
% 0.75/0.95  
% 0.75/0.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
