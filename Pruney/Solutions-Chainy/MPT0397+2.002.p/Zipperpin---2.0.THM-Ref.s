%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OANEqfLotA

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:55 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   39 (  52 expanded)
%              Number of leaves         :   13 (  21 expanded)
%              Depth                    :   12
%              Number of atoms          :  292 ( 440 expanded)
%              Number of equality atoms :   14 (  26 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r2_setfam_1_type,type,(
    r2_setfam_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t19_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_setfam_1 @ B @ A )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_setfam_1 @ B @ A )
       => ( ( A = k1_xboole_0 )
          | ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t19_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ ( k1_setfam_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_setfam_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ B @ C ) )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X6 @ X5 ) @ X5 )
      | ( r1_tarski @ X6 @ ( k1_setfam_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf(d3_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_setfam_1 @ A @ B )
    <=> ! [C: $i] :
          ~ ( ( r2_hidden @ C @ B )
            & ! [D: $i] :
                ~ ( ( r2_hidden @ D @ A )
                  & ( r1_tarski @ D @ C ) ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( sk_D @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_setfam_1 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_setfam_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ ( k1_setfam_1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ~ ( r2_setfam_1 @ X2 @ X0 )
      | ( r1_tarski @ ( sk_D @ ( sk_C_1 @ X1 @ X0 ) @ X2 ) @ ( sk_C_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_D @ ( sk_C_1 @ X0 @ sk_A ) @ sk_B ) @ ( sk_C_1 @ X0 @ sk_A ) )
      | ( sk_A = k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_D @ ( sk_C_1 @ X0 @ sk_A ) @ sk_B ) @ ( sk_C_1 @ X0 @ sk_A ) )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X6 @ X5 ) @ X5 )
      | ( r1_tarski @ X6 @ ( k1_setfam_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf('9',plain,(
    r2_setfam_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_setfam_1 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_setfam_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ ( sk_C_1 @ X0 @ sk_A ) @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ ( sk_C_1 @ X0 @ sk_A ) @ sk_B ) @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf(t8_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ C ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_tarski @ X7 @ X9 )
      | ( r1_tarski @ ( k1_setfam_1 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t8_setfam_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_A ) )
      | ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ X1 )
      | ~ ( r1_tarski @ ( sk_D @ ( sk_C_1 @ X0 @ sk_A ) @ sk_B ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_A ) )
      | ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ ( sk_C_1 @ X0 @ sk_A ) )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ ( sk_C_1 @ X0 @ sk_A ) )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ ( sk_C_1 @ X6 @ X5 ) )
      | ( r1_tarski @ X6 @ ( k1_setfam_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf('20',plain,
    ( ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ ( k1_setfam_1 @ sk_A ) )
    | ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ ( k1_setfam_1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ ( k1_setfam_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    r1_tarski @ ( k1_setfam_1 @ sk_B ) @ ( k1_setfam_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('24',plain,(
    $false ),
    inference(demod,[status(thm)],['0','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OANEqfLotA
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:26:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 45 iterations in 0.047s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.50  thf(r2_setfam_1_type, type, r2_setfam_1: $i > $i > $o).
% 0.20/0.50  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(t19_setfam_1, conjecture,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r2_setfam_1 @ B @ A ) =>
% 0.20/0.50       ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.50         ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i]:
% 0.20/0.50        ( ( r2_setfam_1 @ B @ A ) =>
% 0.20/0.50          ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.50            ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t19_setfam_1])).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      (~ (r1_tarski @ (k1_setfam_1 @ sk_B) @ (k1_setfam_1 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('1', plain, ((r2_setfam_1 @ sk_B @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t6_setfam_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ B @ C ) ) ) =>
% 0.20/0.50       ( ( ( A ) = ( k1_xboole_0 ) ) | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X5 : $i, X6 : $i]:
% 0.20/0.50         (((X5) = (k1_xboole_0))
% 0.20/0.50          | (r2_hidden @ (sk_C_1 @ X6 @ X5) @ X5)
% 0.20/0.50          | (r1_tarski @ X6 @ (k1_setfam_1 @ X5)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.20/0.50  thf(d3_setfam_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r2_setfam_1 @ A @ B ) <=>
% 0.20/0.50       ( ![C:$i]:
% 0.20/0.50         ( ~( ( r2_hidden @ C @ B ) & 
% 0.20/0.50              ( ![D:$i]: ( ~( ( r2_hidden @ D @ A ) & ( r1_tarski @ D @ C ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         ((r1_tarski @ (sk_D @ X0 @ X1) @ X0)
% 0.20/0.50          | ~ (r2_hidden @ X0 @ X2)
% 0.20/0.50          | ~ (r2_setfam_1 @ X1 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_setfam_1])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         ((r1_tarski @ X1 @ (k1_setfam_1 @ X0))
% 0.20/0.50          | ((X0) = (k1_xboole_0))
% 0.20/0.50          | ~ (r2_setfam_1 @ X2 @ X0)
% 0.20/0.50          | (r1_tarski @ (sk_D @ (sk_C_1 @ X1 @ X0) @ X2) @ (sk_C_1 @ X1 @ X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r1_tarski @ (sk_D @ (sk_C_1 @ X0 @ sk_A) @ sk_B) @ 
% 0.20/0.50           (sk_C_1 @ X0 @ sk_A))
% 0.20/0.50          | ((sk_A) = (k1_xboole_0))
% 0.20/0.50          | (r1_tarski @ X0 @ (k1_setfam_1 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['1', '4'])).
% 0.20/0.50  thf('6', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r1_tarski @ (sk_D @ (sk_C_1 @ X0 @ sk_A) @ sk_B) @ 
% 0.20/0.50           (sk_C_1 @ X0 @ sk_A))
% 0.20/0.50          | (r1_tarski @ X0 @ (k1_setfam_1 @ sk_A)))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X5 : $i, X6 : $i]:
% 0.20/0.50         (((X5) = (k1_xboole_0))
% 0.20/0.50          | (r2_hidden @ (sk_C_1 @ X6 @ X5) @ X5)
% 0.20/0.50          | (r1_tarski @ X6 @ (k1_setfam_1 @ X5)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.20/0.50  thf('9', plain, ((r2_setfam_1 @ sk_B @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         ((r2_hidden @ (sk_D @ X0 @ X1) @ X1)
% 0.20/0.50          | ~ (r2_hidden @ X0 @ X2)
% 0.20/0.50          | ~ (r2_setfam_1 @ X1 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_setfam_1])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X0 @ sk_A) | (r2_hidden @ (sk_D @ X0 @ sk_B) @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r1_tarski @ X0 @ (k1_setfam_1 @ sk_A))
% 0.20/0.50          | ((sk_A) = (k1_xboole_0))
% 0.20/0.50          | (r2_hidden @ (sk_D @ (sk_C_1 @ X0 @ sk_A) @ sk_B) @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['8', '11'])).
% 0.20/0.50  thf('13', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r1_tarski @ X0 @ (k1_setfam_1 @ sk_A))
% 0.20/0.50          | (r2_hidden @ (sk_D @ (sk_C_1 @ X0 @ sk_A) @ sk_B) @ sk_B))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.20/0.50  thf(t8_setfam_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( r2_hidden @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.20/0.50       ( r1_tarski @ ( k1_setfam_1 @ B ) @ C ) ))).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X7 @ X8)
% 0.20/0.50          | ~ (r1_tarski @ X7 @ X9)
% 0.20/0.50          | (r1_tarski @ (k1_setfam_1 @ X8) @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [t8_setfam_1])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r1_tarski @ X0 @ (k1_setfam_1 @ sk_A))
% 0.20/0.50          | (r1_tarski @ (k1_setfam_1 @ sk_B) @ X1)
% 0.20/0.50          | ~ (r1_tarski @ (sk_D @ (sk_C_1 @ X0 @ sk_A) @ sk_B) @ X1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r1_tarski @ X0 @ (k1_setfam_1 @ sk_A))
% 0.20/0.51          | (r1_tarski @ (k1_setfam_1 @ sk_B) @ (sk_C_1 @ X0 @ sk_A))
% 0.20/0.51          | (r1_tarski @ X0 @ (k1_setfam_1 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['7', '16'])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r1_tarski @ (k1_setfam_1 @ sk_B) @ (sk_C_1 @ X0 @ sk_A))
% 0.20/0.51          | (r1_tarski @ X0 @ (k1_setfam_1 @ sk_A)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (![X5 : $i, X6 : $i]:
% 0.20/0.51         (((X5) = (k1_xboole_0))
% 0.20/0.51          | ~ (r1_tarski @ X6 @ (sk_C_1 @ X6 @ X5))
% 0.20/0.51          | (r1_tarski @ X6 @ (k1_setfam_1 @ X5)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (((r1_tarski @ (k1_setfam_1 @ sk_B) @ (k1_setfam_1 @ sk_A))
% 0.20/0.51        | (r1_tarski @ (k1_setfam_1 @ sk_B) @ (k1_setfam_1 @ sk_A))
% 0.20/0.51        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      ((((sk_A) = (k1_xboole_0))
% 0.20/0.51        | (r1_tarski @ (k1_setfam_1 @ sk_B) @ (k1_setfam_1 @ sk_A)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.51  thf('22', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('23', plain, ((r1_tarski @ (k1_setfam_1 @ sk_B) @ (k1_setfam_1 @ sk_A))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.20/0.51  thf('24', plain, ($false), inference('demod', [status(thm)], ['0', '23'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
