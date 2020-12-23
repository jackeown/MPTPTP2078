%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hiScaVacNK

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:52 EST 2020

% Result     : Theorem 0.78s
% Output     : Refutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :   50 (  81 expanded)
%              Number of leaves         :   13 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :  444 ( 875 expanded)
%              Number of equality atoms :   45 (  77 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t140_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k2_xboole_0 @ ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t140_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('2',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('6',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = ( k4_xboole_0 @ X2 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('8',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X17 )
      | ( X18 = X15 )
      | ( X17
       != ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('9',plain,(
    ! [X15: $i,X18: $i] :
      ( ( X18 = X15 )
      | ~ ( r2_hidden @ X18 @ ( k1_tarski @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X2 )
        = ( k4_xboole_0 @ X1 @ X1 ) )
      | ( ( sk_D @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) @ X1 @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('12',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('13',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = ( k4_xboole_0 @ X2 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k4_xboole_0 @ X2 @ X2 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k4_xboole_0 @ X2 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k4_xboole_0 @ X2 @ X2 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','16'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = ( k4_xboole_0 @ X2 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = ( k4_xboole_0 @ X2 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('26',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','27'])).

thf('29',plain,(
    ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('31',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
 != sk_B ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('34',plain,(
    ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['28','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hiScaVacNK
% 0.13/0.38  % Computer   : n006.cluster.edu
% 0.13/0.38  % Model      : x86_64 x86_64
% 0.13/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.38  % Memory     : 8042.1875MB
% 0.13/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.38  % CPULimit   : 60
% 0.13/0.38  % DateTime   : Tue Dec  1 11:14:23 EST 2020
% 0.13/0.38  % CPUTime    : 
% 0.13/0.38  % Running portfolio for 600 s
% 0.13/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.38  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.78/0.97  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.78/0.97  % Solved by: fo/fo7.sh
% 0.78/0.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.78/0.97  % done 361 iterations in 0.478s
% 0.78/0.97  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.78/0.97  % SZS output start Refutation
% 0.78/0.97  thf(sk_A_type, type, sk_A: $i).
% 0.78/0.97  thf(sk_B_type, type, sk_B: $i).
% 0.78/0.97  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.78/0.97  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.78/0.97  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.78/0.97  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.78/0.97  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.78/0.97  thf(t140_zfmisc_1, conjecture,
% 0.78/0.97    (![A:$i,B:$i]:
% 0.78/0.97     ( ( r2_hidden @ A @ B ) =>
% 0.78/0.97       ( ( k2_xboole_0 @
% 0.78/0.97           ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.78/0.97         ( B ) ) ))).
% 0.78/0.97  thf(zf_stmt_0, negated_conjecture,
% 0.78/0.97    (~( ![A:$i,B:$i]:
% 0.78/0.97        ( ( r2_hidden @ A @ B ) =>
% 0.78/0.97          ( ( k2_xboole_0 @
% 0.78/0.97              ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.78/0.97            ( B ) ) ) )),
% 0.78/0.97    inference('cnf.neg', [status(esa)], [t140_zfmisc_1])).
% 0.78/0.97  thf('0', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.78/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.97  thf(d5_xboole_0, axiom,
% 0.78/0.97    (![A:$i,B:$i,C:$i]:
% 0.78/0.97     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.78/0.97       ( ![D:$i]:
% 0.78/0.97         ( ( r2_hidden @ D @ C ) <=>
% 0.78/0.97           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.78/0.97  thf('1', plain,
% 0.78/0.97      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.78/0.97         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 0.78/0.97          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.78/0.97          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.78/0.97      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.78/0.97  thf('2', plain,
% 0.78/0.97      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.78/0.97         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 0.78/0.97          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 0.78/0.97          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.78/0.97      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.78/0.97  thf('3', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i]:
% 0.78/0.97         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.78/0.97          | ((X1) = (k4_xboole_0 @ X0 @ X0))
% 0.78/0.97          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.78/0.97          | ((X1) = (k4_xboole_0 @ X0 @ X0)))),
% 0.78/0.97      inference('sup-', [status(thm)], ['1', '2'])).
% 0.78/0.97  thf('4', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i]:
% 0.78/0.97         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 0.78/0.97          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 0.78/0.97      inference('simplify', [status(thm)], ['3'])).
% 0.78/0.97  thf('5', plain,
% 0.78/0.97      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.78/0.97         (~ (r2_hidden @ X6 @ X5)
% 0.78/0.97          | (r2_hidden @ X6 @ X3)
% 0.78/0.97          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.78/0.97      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.78/0.97  thf('6', plain,
% 0.78/0.97      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.78/0.97         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.78/0.97      inference('simplify', [status(thm)], ['5'])).
% 0.78/0.97  thf('7', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/0.97         (((k4_xboole_0 @ X1 @ X0) = (k4_xboole_0 @ X2 @ X2))
% 0.78/0.97          | (r2_hidden @ (sk_D @ (k4_xboole_0 @ X1 @ X0) @ X2 @ X2) @ X1))),
% 0.78/0.97      inference('sup-', [status(thm)], ['4', '6'])).
% 0.78/0.97  thf(d1_tarski, axiom,
% 0.78/0.97    (![A:$i,B:$i]:
% 0.78/0.97     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.78/0.97       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.78/0.97  thf('8', plain,
% 0.78/0.97      (![X15 : $i, X17 : $i, X18 : $i]:
% 0.78/0.97         (~ (r2_hidden @ X18 @ X17)
% 0.78/0.97          | ((X18) = (X15))
% 0.78/0.97          | ((X17) != (k1_tarski @ X15)))),
% 0.78/0.97      inference('cnf', [status(esa)], [d1_tarski])).
% 0.78/0.97  thf('9', plain,
% 0.78/0.97      (![X15 : $i, X18 : $i]:
% 0.78/0.97         (((X18) = (X15)) | ~ (r2_hidden @ X18 @ (k1_tarski @ X15)))),
% 0.78/0.97      inference('simplify', [status(thm)], ['8'])).
% 0.78/0.97  thf('10', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/0.97         (((k4_xboole_0 @ (k1_tarski @ X0) @ X2) = (k4_xboole_0 @ X1 @ X1))
% 0.78/0.97          | ((sk_D @ (k4_xboole_0 @ (k1_tarski @ X0) @ X2) @ X1 @ X1) = (X0)))),
% 0.78/0.97      inference('sup-', [status(thm)], ['7', '9'])).
% 0.78/0.97  thf('11', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i]:
% 0.78/0.97         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 0.78/0.97          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 0.78/0.97      inference('simplify', [status(thm)], ['3'])).
% 0.78/0.97  thf('12', plain,
% 0.78/0.97      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.78/0.97         (~ (r2_hidden @ X6 @ X5)
% 0.78/0.97          | ~ (r2_hidden @ X6 @ X4)
% 0.78/0.97          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.78/0.97      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.78/0.97  thf('13', plain,
% 0.78/0.97      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.78/0.97         (~ (r2_hidden @ X6 @ X4)
% 0.78/0.97          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.78/0.97      inference('simplify', [status(thm)], ['12'])).
% 0.78/0.97  thf('14', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/0.97         (((k4_xboole_0 @ X1 @ X0) = (k4_xboole_0 @ X2 @ X2))
% 0.78/0.97          | ~ (r2_hidden @ (sk_D @ (k4_xboole_0 @ X1 @ X0) @ X2 @ X2) @ X0))),
% 0.78/0.97      inference('sup-', [status(thm)], ['11', '13'])).
% 0.78/0.97  thf('15', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/0.97         (~ (r2_hidden @ X0 @ X1)
% 0.78/0.97          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k4_xboole_0 @ X2 @ X2))
% 0.78/0.97          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k4_xboole_0 @ X2 @ X2)))),
% 0.78/0.97      inference('sup-', [status(thm)], ['10', '14'])).
% 0.78/0.97  thf('16', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/0.97         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k4_xboole_0 @ X2 @ X2))
% 0.78/0.97          | ~ (r2_hidden @ X0 @ X1))),
% 0.78/0.97      inference('simplify', [status(thm)], ['15'])).
% 0.78/0.97  thf('17', plain,
% 0.78/0.97      (![X0 : $i]:
% 0.78/0.97         ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k4_xboole_0 @ X0 @ X0))),
% 0.78/0.97      inference('sup-', [status(thm)], ['0', '16'])).
% 0.78/0.97  thf(t39_xboole_1, axiom,
% 0.78/0.97    (![A:$i,B:$i]:
% 0.78/0.97     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.78/0.97  thf('18', plain,
% 0.78/0.97      (![X11 : $i, X12 : $i]:
% 0.78/0.97         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 0.78/0.97           = (k2_xboole_0 @ X11 @ X12))),
% 0.78/0.97      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.78/0.97  thf('19', plain,
% 0.78/0.97      (![X0 : $i]:
% 0.78/0.97         ((k2_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ X0))
% 0.78/0.97           = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.78/0.97      inference('sup+', [status(thm)], ['17', '18'])).
% 0.78/0.97  thf('20', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/0.97         (((k4_xboole_0 @ X1 @ X0) = (k4_xboole_0 @ X2 @ X2))
% 0.78/0.97          | (r2_hidden @ (sk_D @ (k4_xboole_0 @ X1 @ X0) @ X2 @ X2) @ X1))),
% 0.78/0.97      inference('sup-', [status(thm)], ['4', '6'])).
% 0.78/0.97  thf('21', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/0.97         (((k4_xboole_0 @ X1 @ X0) = (k4_xboole_0 @ X2 @ X2))
% 0.78/0.97          | ~ (r2_hidden @ (sk_D @ (k4_xboole_0 @ X1 @ X0) @ X2 @ X2) @ X0))),
% 0.78/0.97      inference('sup-', [status(thm)], ['11', '13'])).
% 0.78/0.97  thf('22', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i]:
% 0.78/0.97         (((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X1 @ X1))
% 0.78/0.97          | ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X1 @ X1)))),
% 0.78/0.97      inference('sup-', [status(thm)], ['20', '21'])).
% 0.78/0.97  thf('23', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X1 @ X1))),
% 0.78/0.97      inference('simplify', [status(thm)], ['22'])).
% 0.78/0.97  thf('24', plain,
% 0.78/0.97      (![X11 : $i, X12 : $i]:
% 0.78/0.97         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 0.78/0.97           = (k2_xboole_0 @ X11 @ X12))),
% 0.78/0.97      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.78/0.97  thf('25', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i]:
% 0.78/0.97         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.78/0.97           = (k2_xboole_0 @ X1 @ X1))),
% 0.78/0.97      inference('sup+', [status(thm)], ['23', '24'])).
% 0.78/0.97  thf(idempotence_k2_xboole_0, axiom,
% 0.78/0.97    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.78/0.97  thf('26', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ X8) = (X8))),
% 0.78/0.97      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.78/0.97  thf('27', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i]:
% 0.78/0.97         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 0.78/0.97      inference('demod', [status(thm)], ['25', '26'])).
% 0.78/0.97  thf('28', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.78/0.97      inference('demod', [status(thm)], ['19', '27'])).
% 0.78/0.97  thf('29', plain,
% 0.78/0.97      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.78/0.97         (k1_tarski @ sk_A)) != (sk_B))),
% 0.78/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.97  thf(commutativity_k2_xboole_0, axiom,
% 0.78/0.97    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.78/0.97  thf('30', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.78/0.97      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.78/0.97  thf('31', plain,
% 0.78/0.97      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.78/0.97         (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) != (sk_B))),
% 0.78/0.97      inference('demod', [status(thm)], ['29', '30'])).
% 0.78/0.97  thf('32', plain,
% 0.78/0.97      (![X11 : $i, X12 : $i]:
% 0.78/0.97         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 0.78/0.97           = (k2_xboole_0 @ X11 @ X12))),
% 0.78/0.97      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.78/0.97  thf('33', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.78/0.97      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.78/0.97  thf('34', plain, (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (sk_B))),
% 0.78/0.97      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.78/0.97  thf('35', plain, ($false),
% 0.78/0.97      inference('simplify_reflect-', [status(thm)], ['28', '34'])).
% 0.78/0.97  
% 0.78/0.97  % SZS output end Refutation
% 0.78/0.97  
% 0.78/0.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
