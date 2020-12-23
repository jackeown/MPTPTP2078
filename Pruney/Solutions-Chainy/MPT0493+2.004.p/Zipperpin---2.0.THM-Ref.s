%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.guKozXfIUs

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:02 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   51 (  59 expanded)
%              Number of leaves         :   21 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :  337 ( 426 expanded)
%              Number of equality atoms :   30 (  38 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t91_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
         => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t91_relat_1])).

thf('1',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ sk_A ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k4_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
      | ( r2_hidden @ ( sk_D @ X0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('9',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('10',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['11'])).

thf('13',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('17',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('18',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X17 ) @ X18 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('19',plain,(
    ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
     != sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('21',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_tarski @ X14 @ X13 )
      = ( k2_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['20','25','26'])).

thf('28',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['17','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.guKozXfIUs
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:16:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.59/0.78  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.78  % Solved by: fo/fo7.sh
% 0.59/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.78  % done 518 iterations in 0.299s
% 0.59/0.78  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.78  % SZS output start Refutation
% 0.59/0.78  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.78  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.59/0.78  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.59/0.78  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.59/0.78  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.59/0.78  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.59/0.78  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.59/0.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.78  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.78  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.59/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.78  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.78  thf(d5_xboole_0, axiom,
% 0.59/0.78    (![A:$i,B:$i,C:$i]:
% 0.59/0.78     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.59/0.78       ( ![D:$i]:
% 0.59/0.78         ( ( r2_hidden @ D @ C ) <=>
% 0.59/0.78           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.59/0.78  thf('0', plain,
% 0.59/0.78      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.59/0.78         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 0.59/0.78          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 0.59/0.78          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.59/0.78      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.59/0.78  thf(t91_relat_1, conjecture,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( v1_relat_1 @ B ) =>
% 0.59/0.78       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.59/0.78         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.59/0.78  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.78    (~( ![A:$i,B:$i]:
% 0.59/0.78        ( ( v1_relat_1 @ B ) =>
% 0.59/0.78          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.59/0.78            ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ) )),
% 0.59/0.78    inference('cnf.neg', [status(esa)], [t91_relat_1])).
% 0.59/0.78  thf('1', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf(d3_tarski, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( r1_tarski @ A @ B ) <=>
% 0.59/0.78       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.59/0.78  thf('2', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.78         (~ (r2_hidden @ X0 @ X1)
% 0.59/0.78          | (r2_hidden @ X0 @ X2)
% 0.59/0.78          | ~ (r1_tarski @ X1 @ X2))),
% 0.59/0.78      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.78  thf('3', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((r2_hidden @ X0 @ (k1_relat_1 @ sk_B)) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.59/0.78      inference('sup-', [status(thm)], ['1', '2'])).
% 0.59/0.78  thf('4', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]:
% 0.59/0.78         ((r2_hidden @ (sk_D @ X1 @ X0 @ sk_A) @ X1)
% 0.59/0.78          | ((X1) = (k4_xboole_0 @ sk_A @ X0))
% 0.59/0.78          | (r2_hidden @ (sk_D @ X1 @ X0 @ sk_A) @ (k1_relat_1 @ sk_B)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['0', '3'])).
% 0.59/0.78  thf('5', plain,
% 0.59/0.78      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.59/0.78         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 0.59/0.78          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 0.59/0.78          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.59/0.78      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.59/0.78  thf('6', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (((X0) = (k4_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.59/0.78          | (r2_hidden @ (sk_D @ X0 @ (k1_relat_1 @ sk_B) @ sk_A) @ X0)
% 0.59/0.78          | (r2_hidden @ (sk_D @ X0 @ (k1_relat_1 @ sk_B) @ sk_A) @ X0)
% 0.59/0.78          | ((X0) = (k4_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['4', '5'])).
% 0.59/0.78  thf('7', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((r2_hidden @ (sk_D @ X0 @ (k1_relat_1 @ sk_B) @ sk_A) @ X0)
% 0.59/0.78          | ((X0) = (k4_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.59/0.78      inference('simplify', [status(thm)], ['6'])).
% 0.59/0.78  thf(t3_boole, axiom,
% 0.59/0.78    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.59/0.78  thf('8', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.59/0.78      inference('cnf', [status(esa)], [t3_boole])).
% 0.59/0.78  thf('9', plain,
% 0.59/0.78      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.59/0.78         (~ (r2_hidden @ X8 @ X7)
% 0.59/0.78          | ~ (r2_hidden @ X8 @ X6)
% 0.59/0.78          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.59/0.78      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.59/0.78  thf('10', plain,
% 0.59/0.78      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.59/0.78         (~ (r2_hidden @ X8 @ X6)
% 0.59/0.78          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.59/0.78      inference('simplify', [status(thm)], ['9'])).
% 0.59/0.78  thf('11', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]:
% 0.59/0.78         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['8', '10'])).
% 0.59/0.78  thf('12', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.59/0.78      inference('condensation', [status(thm)], ['11'])).
% 0.59/0.78  thf('13', plain,
% 0.59/0.78      (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['7', '12'])).
% 0.59/0.78  thf(t48_xboole_1, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.59/0.78  thf('14', plain,
% 0.59/0.78      (![X11 : $i, X12 : $i]:
% 0.59/0.78         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.59/0.78           = (k3_xboole_0 @ X11 @ X12))),
% 0.59/0.78      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.59/0.78  thf('15', plain,
% 0.59/0.78      (((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.59/0.78         = (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.59/0.78      inference('sup+', [status(thm)], ['13', '14'])).
% 0.59/0.78  thf('16', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.59/0.78      inference('cnf', [status(esa)], [t3_boole])).
% 0.59/0.78  thf('17', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.59/0.78      inference('demod', [status(thm)], ['15', '16'])).
% 0.59/0.78  thf(t90_relat_1, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( v1_relat_1 @ B ) =>
% 0.59/0.78       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.59/0.78         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.59/0.78  thf('18', plain,
% 0.59/0.78      (![X17 : $i, X18 : $i]:
% 0.59/0.78         (((k1_relat_1 @ (k7_relat_1 @ X17 @ X18))
% 0.59/0.78            = (k3_xboole_0 @ (k1_relat_1 @ X17) @ X18))
% 0.59/0.78          | ~ (v1_relat_1 @ X17))),
% 0.59/0.78      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.59/0.78  thf('19', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) != (sk_A))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('20', plain,
% 0.59/0.78      ((((k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A) != (sk_A))
% 0.59/0.78        | ~ (v1_relat_1 @ sk_B))),
% 0.59/0.78      inference('sup-', [status(thm)], ['18', '19'])).
% 0.59/0.78  thf(commutativity_k2_tarski, axiom,
% 0.59/0.78    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.59/0.78  thf('21', plain,
% 0.59/0.78      (![X13 : $i, X14 : $i]:
% 0.59/0.78         ((k2_tarski @ X14 @ X13) = (k2_tarski @ X13 @ X14))),
% 0.59/0.78      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.59/0.78  thf(t12_setfam_1, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.59/0.78  thf('22', plain,
% 0.59/0.78      (![X15 : $i, X16 : $i]:
% 0.59/0.78         ((k1_setfam_1 @ (k2_tarski @ X15 @ X16)) = (k3_xboole_0 @ X15 @ X16))),
% 0.59/0.78      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.59/0.78  thf('23', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]:
% 0.59/0.78         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.78      inference('sup+', [status(thm)], ['21', '22'])).
% 0.59/0.78  thf('24', plain,
% 0.59/0.78      (![X15 : $i, X16 : $i]:
% 0.59/0.78         ((k1_setfam_1 @ (k2_tarski @ X15 @ X16)) = (k3_xboole_0 @ X15 @ X16))),
% 0.59/0.78      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.59/0.78  thf('25', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.78      inference('sup+', [status(thm)], ['23', '24'])).
% 0.59/0.78  thf('26', plain, ((v1_relat_1 @ sk_B)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('27', plain, (((k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) != (sk_A))),
% 0.59/0.78      inference('demod', [status(thm)], ['20', '25', '26'])).
% 0.59/0.78  thf('28', plain, ($false),
% 0.59/0.78      inference('simplify_reflect-', [status(thm)], ['17', '27'])).
% 0.59/0.78  
% 0.59/0.78  % SZS output end Refutation
% 0.59/0.78  
% 0.59/0.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
