%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vCwzGBf6ii

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:44 EST 2020

% Result     : Theorem 0.57s
% Output     : Refutation 0.57s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 111 expanded)
%              Number of leaves         :   18 (  37 expanded)
%              Depth                    :   17
%              Number of atoms          :  453 (1222 expanded)
%              Number of equality atoms :   70 ( 190 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(d1_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( A = k1_xboole_0 )
       => ( ( B
            = ( k1_setfam_1 @ A ) )
        <=> ( B = k1_xboole_0 ) ) )
      & ( ( A != k1_xboole_0 )
       => ( ( B
            = ( k1_setfam_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ! [D: $i] :
                  ( ( r2_hidden @ D @ A )
                 => ( r2_hidden @ C @ D ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X25: $i,X30: $i] :
      ( ( X30
       != ( k1_setfam_1 @ X25 ) )
      | ( X30 = k1_xboole_0 )
      | ( X25 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('1',plain,
    ( ( k1_setfam_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['0'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('4',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r2_hidden @ ( sk_C @ X24 @ X25 ) @ X24 )
      | ( r2_hidden @ ( sk_C @ X24 @ X25 ) @ X26 )
      | ~ ( r2_hidden @ X26 @ X25 )
      | ( X24
        = ( k1_setfam_1 @ X25 ) )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X1
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_tarski @ X0 ) ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_tarski @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ X0 ) ) @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(eq_fact,[status(thm)],['7'])).

thf('9',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X24 @ X25 ) @ X24 )
      | ( r2_hidden @ ( sk_D_1 @ X24 @ X25 ) @ X25 )
      | ( X24
        = ( k1_setfam_1 @ X25 ) )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('12',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) )
        = ( k1_tarski @ X16 ) )
      | ( X16 = X17 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('13',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X18 != X20 )
      | ~ ( r2_hidden @ X18 @ ( k4_xboole_0 @ X19 @ ( k1_tarski @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('14',plain,(
    ! [X19: $i,X20: $i] :
      ~ ( r2_hidden @ X20 @ ( k4_xboole_0 @ X19 @ ( k1_tarski @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( X0
        = ( sk_D_1 @ X0 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X24 @ X25 ) @ X24 )
      | ~ ( r2_hidden @ ( sk_C @ X24 @ X25 ) @ ( sk_D_1 @ X24 @ X25 ) )
      | ( X24
        = ( k1_setfam_1 @ X25 ) )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ X0 ) ) @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ X0 ) ) @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(eq_fact,[status(thm)],['7'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf(t11_setfam_1,conjecture,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t11_setfam_1])).

thf('22',plain,(
    ( k1_setfam_1 @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( sk_A != sk_A )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['23'])).

thf(t6_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf('25',plain,(
    ! [X22: $i,X23: $i] :
      ( ( X23 = X22 )
      | ~ ( r1_tarski @ ( k1_tarski @ X23 ) @ ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t6_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( sk_A = X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('27',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ ( k1_tarski @ X14 ) )
      | ( X13 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('28',plain,(
    ! [X14: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X14 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference(demod,[status(thm)],['26','28'])).

thf('30',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['1','29'])).

thf('31',plain,(
    ( k1_setfam_1 @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['23'])).

thf('33',plain,
    ( ( k1_setfam_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['0'])).

thf('34',plain,(
    k1_xboole_0 != sk_A ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['30','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vCwzGBf6ii
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:28:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.57/0.76  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.57/0.76  % Solved by: fo/fo7.sh
% 0.57/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.57/0.76  % done 463 iterations in 0.314s
% 0.57/0.76  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.57/0.76  % SZS output start Refutation
% 0.57/0.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.57/0.76  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.57/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.57/0.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.57/0.76  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.57/0.76  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.57/0.76  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.57/0.76  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.57/0.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.57/0.76  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.57/0.76  thf(d1_setfam_1, axiom,
% 0.57/0.76    (![A:$i,B:$i]:
% 0.57/0.76     ( ( ( ( A ) = ( k1_xboole_0 ) ) =>
% 0.57/0.76         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=> ( ( B ) = ( k1_xboole_0 ) ) ) ) & 
% 0.57/0.76       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.57/0.76         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=>
% 0.57/0.76           ( ![C:$i]:
% 0.57/0.76             ( ( r2_hidden @ C @ B ) <=>
% 0.57/0.76               ( ![D:$i]: ( ( r2_hidden @ D @ A ) => ( r2_hidden @ C @ D ) ) ) ) ) ) ) ))).
% 0.57/0.76  thf('0', plain,
% 0.57/0.76      (![X25 : $i, X30 : $i]:
% 0.57/0.76         (((X30) != (k1_setfam_1 @ X25))
% 0.57/0.76          | ((X30) = (k1_xboole_0))
% 0.57/0.76          | ((X25) != (k1_xboole_0)))),
% 0.57/0.76      inference('cnf', [status(esa)], [d1_setfam_1])).
% 0.57/0.76  thf('1', plain, (((k1_setfam_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.57/0.76      inference('simplify', [status(thm)], ['0'])).
% 0.57/0.76  thf(t69_enumset1, axiom,
% 0.57/0.76    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.57/0.76  thf('2', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.57/0.76      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.57/0.76  thf(d2_tarski, axiom,
% 0.57/0.76    (![A:$i,B:$i,C:$i]:
% 0.57/0.76     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.57/0.76       ( ![D:$i]:
% 0.57/0.76         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.57/0.76  thf('3', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.57/0.76         (((X1) != (X0))
% 0.57/0.76          | (r2_hidden @ X1 @ X2)
% 0.57/0.76          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.57/0.76      inference('cnf', [status(esa)], [d2_tarski])).
% 0.57/0.76  thf('4', plain,
% 0.57/0.76      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.57/0.76      inference('simplify', [status(thm)], ['3'])).
% 0.57/0.76  thf('5', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.57/0.76      inference('sup+', [status(thm)], ['2', '4'])).
% 0.57/0.76  thf('6', plain,
% 0.57/0.76      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.57/0.76         ((r2_hidden @ (sk_C @ X24 @ X25) @ X24)
% 0.57/0.76          | (r2_hidden @ (sk_C @ X24 @ X25) @ X26)
% 0.57/0.76          | ~ (r2_hidden @ X26 @ X25)
% 0.57/0.76          | ((X24) = (k1_setfam_1 @ X25))
% 0.57/0.76          | ((X25) = (k1_xboole_0)))),
% 0.57/0.76      inference('cnf', [status(esa)], [d1_setfam_1])).
% 0.57/0.76  thf('7', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i]:
% 0.57/0.76         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.57/0.76          | ((X1) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.57/0.76          | (r2_hidden @ (sk_C @ X1 @ (k1_tarski @ X0)) @ X0)
% 0.57/0.76          | (r2_hidden @ (sk_C @ X1 @ (k1_tarski @ X0)) @ X1))),
% 0.57/0.76      inference('sup-', [status(thm)], ['5', '6'])).
% 0.57/0.76  thf('8', plain,
% 0.57/0.76      (![X0 : $i]:
% 0.57/0.76         ((r2_hidden @ (sk_C @ X0 @ (k1_tarski @ X0)) @ X0)
% 0.57/0.76          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.57/0.76          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.57/0.76      inference('eq_fact', [status(thm)], ['7'])).
% 0.57/0.76  thf('9', plain,
% 0.57/0.76      (![X24 : $i, X25 : $i]:
% 0.57/0.76         (~ (r2_hidden @ (sk_C @ X24 @ X25) @ X24)
% 0.57/0.76          | (r2_hidden @ (sk_D_1 @ X24 @ X25) @ X25)
% 0.57/0.76          | ((X24) = (k1_setfam_1 @ X25))
% 0.57/0.76          | ((X25) = (k1_xboole_0)))),
% 0.57/0.76      inference('cnf', [status(esa)], [d1_setfam_1])).
% 0.57/0.76  thf('10', plain,
% 0.57/0.76      (![X0 : $i]:
% 0.57/0.76         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.57/0.76          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.57/0.76          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.57/0.76          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.57/0.76          | (r2_hidden @ (sk_D_1 @ X0 @ (k1_tarski @ X0)) @ (k1_tarski @ X0)))),
% 0.57/0.76      inference('sup-', [status(thm)], ['8', '9'])).
% 0.57/0.76  thf('11', plain,
% 0.57/0.76      (![X0 : $i]:
% 0.57/0.76         ((r2_hidden @ (sk_D_1 @ X0 @ (k1_tarski @ X0)) @ (k1_tarski @ X0))
% 0.57/0.76          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.57/0.76          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.57/0.76      inference('simplify', [status(thm)], ['10'])).
% 0.57/0.76  thf(t20_zfmisc_1, axiom,
% 0.57/0.76    (![A:$i,B:$i]:
% 0.57/0.76     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.57/0.76         ( k1_tarski @ A ) ) <=>
% 0.57/0.76       ( ( A ) != ( B ) ) ))).
% 0.57/0.76  thf('12', plain,
% 0.57/0.76      (![X16 : $i, X17 : $i]:
% 0.57/0.76         (((k4_xboole_0 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 0.57/0.76            = (k1_tarski @ X16))
% 0.57/0.76          | ((X16) = (X17)))),
% 0.57/0.76      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.57/0.76  thf(t64_zfmisc_1, axiom,
% 0.57/0.76    (![A:$i,B:$i,C:$i]:
% 0.57/0.76     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.57/0.76       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.57/0.76  thf('13', plain,
% 0.57/0.76      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.57/0.76         (((X18) != (X20))
% 0.57/0.76          | ~ (r2_hidden @ X18 @ (k4_xboole_0 @ X19 @ (k1_tarski @ X20))))),
% 0.57/0.76      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.57/0.76  thf('14', plain,
% 0.57/0.76      (![X19 : $i, X20 : $i]:
% 0.57/0.76         ~ (r2_hidden @ X20 @ (k4_xboole_0 @ X19 @ (k1_tarski @ X20)))),
% 0.57/0.76      inference('simplify', [status(thm)], ['13'])).
% 0.57/0.76  thf('15', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i]:
% 0.57/0.76         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X0) = (X1)))),
% 0.57/0.76      inference('sup-', [status(thm)], ['12', '14'])).
% 0.57/0.76  thf('16', plain,
% 0.57/0.76      (![X0 : $i]:
% 0.57/0.76         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.57/0.76          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.57/0.76          | ((X0) = (sk_D_1 @ X0 @ (k1_tarski @ X0))))),
% 0.57/0.76      inference('sup-', [status(thm)], ['11', '15'])).
% 0.57/0.76  thf('17', plain,
% 0.57/0.76      (![X24 : $i, X25 : $i]:
% 0.57/0.76         (~ (r2_hidden @ (sk_C @ X24 @ X25) @ X24)
% 0.57/0.76          | ~ (r2_hidden @ (sk_C @ X24 @ X25) @ (sk_D_1 @ X24 @ X25))
% 0.57/0.76          | ((X24) = (k1_setfam_1 @ X25))
% 0.57/0.76          | ((X25) = (k1_xboole_0)))),
% 0.57/0.76      inference('cnf', [status(esa)], [d1_setfam_1])).
% 0.57/0.76  thf('18', plain,
% 0.57/0.76      (![X0 : $i]:
% 0.57/0.76         (~ (r2_hidden @ (sk_C @ X0 @ (k1_tarski @ X0)) @ X0)
% 0.57/0.76          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.57/0.76          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.57/0.76          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.57/0.76          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.57/0.76          | ~ (r2_hidden @ (sk_C @ X0 @ (k1_tarski @ X0)) @ X0))),
% 0.57/0.76      inference('sup-', [status(thm)], ['16', '17'])).
% 0.57/0.76  thf('19', plain,
% 0.57/0.76      (![X0 : $i]:
% 0.57/0.76         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.57/0.76          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.57/0.76          | ~ (r2_hidden @ (sk_C @ X0 @ (k1_tarski @ X0)) @ X0))),
% 0.57/0.76      inference('simplify', [status(thm)], ['18'])).
% 0.57/0.76  thf('20', plain,
% 0.57/0.76      (![X0 : $i]:
% 0.57/0.76         ((r2_hidden @ (sk_C @ X0 @ (k1_tarski @ X0)) @ X0)
% 0.57/0.76          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.57/0.76          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.57/0.76      inference('eq_fact', [status(thm)], ['7'])).
% 0.57/0.76  thf('21', plain,
% 0.57/0.76      (![X0 : $i]:
% 0.57/0.76         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.57/0.76          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.57/0.76      inference('clc', [status(thm)], ['19', '20'])).
% 0.57/0.76  thf(t11_setfam_1, conjecture,
% 0.57/0.76    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.57/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.57/0.76    (~( ![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ) )),
% 0.57/0.76    inference('cnf.neg', [status(esa)], [t11_setfam_1])).
% 0.57/0.76  thf('22', plain, (((k1_setfam_1 @ (k1_tarski @ sk_A)) != (sk_A))),
% 0.57/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.76  thf('23', plain,
% 0.57/0.76      ((((sk_A) != (sk_A)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.57/0.76      inference('sup-', [status(thm)], ['21', '22'])).
% 0.57/0.76  thf('24', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.57/0.76      inference('simplify', [status(thm)], ['23'])).
% 0.57/0.76  thf(t6_zfmisc_1, axiom,
% 0.57/0.76    (![A:$i,B:$i]:
% 0.57/0.76     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.57/0.76       ( ( A ) = ( B ) ) ))).
% 0.57/0.76  thf('25', plain,
% 0.57/0.76      (![X22 : $i, X23 : $i]:
% 0.57/0.76         (((X23) = (X22))
% 0.57/0.76          | ~ (r1_tarski @ (k1_tarski @ X23) @ (k1_tarski @ X22)))),
% 0.57/0.76      inference('cnf', [status(esa)], [t6_zfmisc_1])).
% 0.57/0.76  thf('26', plain,
% 0.57/0.76      (![X0 : $i]:
% 0.57/0.76         (~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) | ((sk_A) = (X0)))),
% 0.57/0.76      inference('sup-', [status(thm)], ['24', '25'])).
% 0.57/0.76  thf(l3_zfmisc_1, axiom,
% 0.57/0.76    (![A:$i,B:$i]:
% 0.57/0.76     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.57/0.76       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.57/0.76  thf('27', plain,
% 0.57/0.76      (![X13 : $i, X14 : $i]:
% 0.57/0.76         ((r1_tarski @ X13 @ (k1_tarski @ X14)) | ((X13) != (k1_xboole_0)))),
% 0.57/0.76      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.57/0.76  thf('28', plain,
% 0.57/0.76      (![X14 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X14))),
% 0.57/0.76      inference('simplify', [status(thm)], ['27'])).
% 0.57/0.76  thf('29', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.57/0.76      inference('demod', [status(thm)], ['26', '28'])).
% 0.57/0.76  thf('30', plain, (((sk_A) = (k1_xboole_0))),
% 0.57/0.76      inference('demod', [status(thm)], ['1', '29'])).
% 0.57/0.76  thf('31', plain, (((k1_setfam_1 @ (k1_tarski @ sk_A)) != (sk_A))),
% 0.57/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.76  thf('32', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.57/0.76      inference('simplify', [status(thm)], ['23'])).
% 0.57/0.76  thf('33', plain, (((k1_setfam_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.57/0.76      inference('simplify', [status(thm)], ['0'])).
% 0.57/0.76  thf('34', plain, (((k1_xboole_0) != (sk_A))),
% 0.57/0.76      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.57/0.76  thf('35', plain, ($false),
% 0.57/0.76      inference('simplify_reflect-', [status(thm)], ['30', '34'])).
% 0.57/0.76  
% 0.57/0.76  % SZS output end Refutation
% 0.57/0.76  
% 0.63/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
