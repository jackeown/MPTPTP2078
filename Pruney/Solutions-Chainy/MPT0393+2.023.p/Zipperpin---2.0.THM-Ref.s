%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rptkrDQZgn

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:43 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   58 (  77 expanded)
%              Number of leaves         :   17 (  28 expanded)
%              Depth                    :   13
%              Number of atoms          :  431 ( 606 expanded)
%              Number of equality atoms :   46 (  67 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ B @ C ) )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X33: $i,X34: $i] :
      ( ( X33 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_2 @ X34 @ X33 ) @ X33 )
      | ( r1_tarski @ X34 @ ( k1_setfam_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( X10 = X7 )
      | ( X9
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('2',plain,(
    ! [X7: $i,X10: $i] :
      ( ( X10 = X7 )
      | ~ ( r2_hidden @ X10 @ ( k1_tarski @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_C_2 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( X8 != X7 )
      | ( r2_hidden @ X8 @ X9 )
      | ( X9
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('5',plain,(
    ! [X7: $i] :
      ( r2_hidden @ X7 @ ( k1_tarski @ X7 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf('6',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X31 ) @ X32 )
      | ~ ( r2_hidden @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_2 @ X0 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    ! [X33: $i,X34: $i] :
      ( ( X33 = k1_xboole_0 )
      | ~ ( r1_tarski @ X34 @ ( sk_C_2 @ X34 @ X33 ) )
      | ( r1_tarski @ X34 @ ( k1_setfam_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf(t11_setfam_1,conjecture,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t11_setfam_1])).

thf('19',plain,(
    ( k1_setfam_1 @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( sk_A != sk_A )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X7: $i] :
      ( r2_hidden @ X7 @ ( k1_tarski @ X7 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('23',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X7: $i] :
      ( r2_hidden @ X7 @ ( k1_tarski @ X7 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('25',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('26',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( r2_hidden @ X27 @ X28 )
      | ~ ( r2_hidden @ X27 @ ( k4_xboole_0 @ X28 @ ( k1_tarski @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) @ X0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('31',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X25
        = ( k1_tarski @ X24 ) )
      | ( X25 = k1_xboole_0 )
      | ~ ( r1_tarski @ X25 @ ( k1_tarski @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( X27 != X29 )
      | ~ ( r2_hidden @ X27 @ ( k4_xboole_0 @ X28 @ ( k1_tarski @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('34',plain,(
    ! [X28: $i,X29: $i] :
      ~ ( r2_hidden @ X29 @ ( k4_xboole_0 @ X28 @ ( k1_tarski @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','35'])).

thf('37',plain,(
    ! [X28: $i,X29: $i] :
      ~ ( r2_hidden @ X29 @ ( k4_xboole_0 @ X28 @ ( k1_tarski @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('38',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    $false ),
    inference('sup-',[status(thm)],['23','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rptkrDQZgn
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:57:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.48/0.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.48/0.69  % Solved by: fo/fo7.sh
% 0.48/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.69  % done 418 iterations in 0.243s
% 0.48/0.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.48/0.69  % SZS output start Refutation
% 0.48/0.69  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.48/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.48/0.69  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.48/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.48/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.48/0.69  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.48/0.69  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.48/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.69  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.48/0.69  thf(t6_setfam_1, axiom,
% 0.48/0.69    (![A:$i,B:$i]:
% 0.48/0.69     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ B @ C ) ) ) =>
% 0.48/0.69       ( ( ( A ) = ( k1_xboole_0 ) ) | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.48/0.69  thf('0', plain,
% 0.48/0.69      (![X33 : $i, X34 : $i]:
% 0.48/0.69         (((X33) = (k1_xboole_0))
% 0.48/0.69          | (r2_hidden @ (sk_C_2 @ X34 @ X33) @ X33)
% 0.48/0.69          | (r1_tarski @ X34 @ (k1_setfam_1 @ X33)))),
% 0.48/0.69      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.48/0.69  thf(d1_tarski, axiom,
% 0.48/0.69    (![A:$i,B:$i]:
% 0.48/0.69     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.48/0.69       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.48/0.69  thf('1', plain,
% 0.48/0.69      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.48/0.69         (~ (r2_hidden @ X10 @ X9)
% 0.48/0.69          | ((X10) = (X7))
% 0.48/0.69          | ((X9) != (k1_tarski @ X7)))),
% 0.48/0.69      inference('cnf', [status(esa)], [d1_tarski])).
% 0.48/0.69  thf('2', plain,
% 0.48/0.69      (![X7 : $i, X10 : $i]:
% 0.48/0.69         (((X10) = (X7)) | ~ (r2_hidden @ X10 @ (k1_tarski @ X7)))),
% 0.48/0.69      inference('simplify', [status(thm)], ['1'])).
% 0.48/0.69  thf('3', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]:
% 0.48/0.69         ((r1_tarski @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.48/0.69          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.48/0.69          | ((sk_C_2 @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.48/0.69      inference('sup-', [status(thm)], ['0', '2'])).
% 0.48/0.69  thf('4', plain,
% 0.48/0.69      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.48/0.69         (((X8) != (X7)) | (r2_hidden @ X8 @ X9) | ((X9) != (k1_tarski @ X7)))),
% 0.48/0.69      inference('cnf', [status(esa)], [d1_tarski])).
% 0.48/0.69  thf('5', plain, (![X7 : $i]: (r2_hidden @ X7 @ (k1_tarski @ X7))),
% 0.48/0.69      inference('simplify', [status(thm)], ['4'])).
% 0.48/0.69  thf(t4_setfam_1, axiom,
% 0.48/0.69    (![A:$i,B:$i]:
% 0.48/0.69     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 0.48/0.69  thf('6', plain,
% 0.48/0.69      (![X31 : $i, X32 : $i]:
% 0.48/0.69         ((r1_tarski @ (k1_setfam_1 @ X31) @ X32) | ~ (r2_hidden @ X32 @ X31))),
% 0.48/0.69      inference('cnf', [status(esa)], [t4_setfam_1])).
% 0.48/0.69  thf('7', plain,
% 0.48/0.69      (![X0 : $i]: (r1_tarski @ (k1_setfam_1 @ (k1_tarski @ X0)) @ X0)),
% 0.48/0.69      inference('sup-', [status(thm)], ['5', '6'])).
% 0.48/0.69  thf(d10_xboole_0, axiom,
% 0.48/0.69    (![A:$i,B:$i]:
% 0.48/0.69     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.48/0.69  thf('8', plain,
% 0.48/0.69      (![X4 : $i, X6 : $i]:
% 0.48/0.69         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.48/0.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.48/0.69  thf('9', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.48/0.69          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.48/0.69      inference('sup-', [status(thm)], ['7', '8'])).
% 0.48/0.69  thf('10', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         (((sk_C_2 @ X0 @ (k1_tarski @ X0)) = (X0))
% 0.48/0.69          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.48/0.69          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.48/0.69      inference('sup-', [status(thm)], ['3', '9'])).
% 0.48/0.69  thf('11', plain,
% 0.48/0.69      (![X33 : $i, X34 : $i]:
% 0.48/0.69         (((X33) = (k1_xboole_0))
% 0.48/0.69          | ~ (r1_tarski @ X34 @ (sk_C_2 @ X34 @ X33))
% 0.48/0.69          | (r1_tarski @ X34 @ (k1_setfam_1 @ X33)))),
% 0.48/0.69      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.48/0.69  thf('12', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         (~ (r1_tarski @ X0 @ X0)
% 0.48/0.69          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.48/0.69          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.48/0.69          | (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.48/0.69          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.48/0.69      inference('sup-', [status(thm)], ['10', '11'])).
% 0.48/0.69  thf('13', plain,
% 0.48/0.69      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.48/0.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.48/0.69  thf('14', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.48/0.69      inference('simplify', [status(thm)], ['13'])).
% 0.48/0.69  thf('15', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.48/0.69          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.48/0.69          | (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.48/0.69          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.48/0.69      inference('demod', [status(thm)], ['12', '14'])).
% 0.48/0.69  thf('16', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.48/0.69          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.48/0.69          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.48/0.69      inference('simplify', [status(thm)], ['15'])).
% 0.48/0.69  thf('17', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.48/0.69          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.48/0.69      inference('sup-', [status(thm)], ['7', '8'])).
% 0.48/0.69  thf('18', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.48/0.69          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.48/0.69      inference('clc', [status(thm)], ['16', '17'])).
% 0.48/0.69  thf(t11_setfam_1, conjecture,
% 0.48/0.69    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.48/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.69    (~( ![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ) )),
% 0.48/0.69    inference('cnf.neg', [status(esa)], [t11_setfam_1])).
% 0.48/0.69  thf('19', plain, (((k1_setfam_1 @ (k1_tarski @ sk_A)) != (sk_A))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('20', plain,
% 0.48/0.69      ((((sk_A) != (sk_A)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.48/0.69      inference('sup-', [status(thm)], ['18', '19'])).
% 0.48/0.69  thf('21', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.48/0.69      inference('simplify', [status(thm)], ['20'])).
% 0.48/0.69  thf('22', plain, (![X7 : $i]: (r2_hidden @ X7 @ (k1_tarski @ X7))),
% 0.48/0.69      inference('simplify', [status(thm)], ['4'])).
% 0.48/0.69  thf('23', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.48/0.69      inference('sup+', [status(thm)], ['21', '22'])).
% 0.48/0.69  thf('24', plain, (![X7 : $i]: (r2_hidden @ X7 @ (k1_tarski @ X7))),
% 0.48/0.69      inference('simplify', [status(thm)], ['4'])).
% 0.48/0.69  thf(d3_tarski, axiom,
% 0.48/0.69    (![A:$i,B:$i]:
% 0.48/0.69     ( ( r1_tarski @ A @ B ) <=>
% 0.48/0.69       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.48/0.69  thf('25', plain,
% 0.48/0.69      (![X1 : $i, X3 : $i]:
% 0.48/0.69         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.48/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.48/0.69  thf(t64_zfmisc_1, axiom,
% 0.48/0.69    (![A:$i,B:$i,C:$i]:
% 0.48/0.69     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.48/0.69       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.48/0.69  thf('26', plain,
% 0.48/0.69      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.48/0.69         ((r2_hidden @ X27 @ X28)
% 0.48/0.69          | ~ (r2_hidden @ X27 @ (k4_xboole_0 @ X28 @ (k1_tarski @ X29))))),
% 0.48/0.69      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.48/0.69  thf('27', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.69         ((r1_tarski @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)) @ X2)
% 0.48/0.69          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0))) @ 
% 0.48/0.69             X1))),
% 0.48/0.69      inference('sup-', [status(thm)], ['25', '26'])).
% 0.48/0.69  thf('28', plain,
% 0.48/0.69      (![X1 : $i, X3 : $i]:
% 0.48/0.69         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.48/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.48/0.69  thf('29', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]:
% 0.48/0.69         ((r1_tarski @ (k4_xboole_0 @ X0 @ (k1_tarski @ X1)) @ X0)
% 0.48/0.69          | (r1_tarski @ (k4_xboole_0 @ X0 @ (k1_tarski @ X1)) @ X0))),
% 0.48/0.69      inference('sup-', [status(thm)], ['27', '28'])).
% 0.48/0.69  thf('30', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]:
% 0.48/0.69         (r1_tarski @ (k4_xboole_0 @ X0 @ (k1_tarski @ X1)) @ X0)),
% 0.48/0.69      inference('simplify', [status(thm)], ['29'])).
% 0.48/0.69  thf(l3_zfmisc_1, axiom,
% 0.48/0.69    (![A:$i,B:$i]:
% 0.48/0.69     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.48/0.69       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.48/0.69  thf('31', plain,
% 0.48/0.69      (![X24 : $i, X25 : $i]:
% 0.48/0.69         (((X25) = (k1_tarski @ X24))
% 0.48/0.69          | ((X25) = (k1_xboole_0))
% 0.48/0.69          | ~ (r1_tarski @ X25 @ (k1_tarski @ X24)))),
% 0.48/0.69      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.48/0.69  thf('32', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]:
% 0.48/0.69         (((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)) = (k1_xboole_0))
% 0.48/0.69          | ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.48/0.69              = (k1_tarski @ X0)))),
% 0.48/0.69      inference('sup-', [status(thm)], ['30', '31'])).
% 0.48/0.69  thf('33', plain,
% 0.48/0.69      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.48/0.69         (((X27) != (X29))
% 0.48/0.69          | ~ (r2_hidden @ X27 @ (k4_xboole_0 @ X28 @ (k1_tarski @ X29))))),
% 0.48/0.69      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.48/0.69  thf('34', plain,
% 0.48/0.69      (![X28 : $i, X29 : $i]:
% 0.48/0.69         ~ (r2_hidden @ X29 @ (k4_xboole_0 @ X28 @ (k1_tarski @ X29)))),
% 0.48/0.69      inference('simplify', [status(thm)], ['33'])).
% 0.48/0.69  thf('35', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]:
% 0.48/0.69         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.48/0.69          | ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.48/0.69              = (k1_xboole_0)))),
% 0.48/0.69      inference('sup-', [status(thm)], ['32', '34'])).
% 0.48/0.69  thf('36', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.48/0.69      inference('sup-', [status(thm)], ['24', '35'])).
% 0.48/0.69  thf('37', plain,
% 0.48/0.69      (![X28 : $i, X29 : $i]:
% 0.48/0.69         ~ (r2_hidden @ X29 @ (k4_xboole_0 @ X28 @ (k1_tarski @ X29)))),
% 0.48/0.69      inference('simplify', [status(thm)], ['33'])).
% 0.48/0.69  thf('38', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.48/0.69      inference('sup-', [status(thm)], ['36', '37'])).
% 0.48/0.69  thf('39', plain, ($false), inference('sup-', [status(thm)], ['23', '38'])).
% 0.48/0.69  
% 0.48/0.69  % SZS output end Refutation
% 0.48/0.69  
% 0.48/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
