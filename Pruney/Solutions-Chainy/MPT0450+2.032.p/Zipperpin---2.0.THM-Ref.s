%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WYF71qWgzm

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   49 (  73 expanded)
%              Number of leaves         :   16 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :  426 ( 687 expanded)
%              Number of equality atoms :   18 (  29 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('2',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('3',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('6',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('14',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t31_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf('16',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( r1_tarski @ ( k3_relat_1 @ X16 ) @ ( k3_relat_1 @ X15 ) )
      | ~ ( r1_tarski @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t31_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(fc2_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( v1_relat_1 @ ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['17','20'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X6 @ X8 )
      | ( r1_tarski @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ X0 ) @ X2 ) )
      | ~ ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ X1 ) @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf(t34_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_relat_1])).

thf('27',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['28','29','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WYF71qWgzm
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:48:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 139 iterations in 0.097s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.55  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.55  thf(d4_xboole_0, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.20/0.55       ( ![D:$i]:
% 0.20/0.55         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.55           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.20/0.55  thf('0', plain,
% 0.20/0.55      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.20/0.55         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.20/0.55          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.20/0.55          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.20/0.55      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.20/0.55  thf('1', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.20/0.55          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.55      inference('eq_fact', [status(thm)], ['0'])).
% 0.20/0.55  thf('2', plain,
% 0.20/0.55      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X4 @ X3)
% 0.20/0.55          | (r2_hidden @ X4 @ X2)
% 0.20/0.55          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.20/0.55      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.20/0.55  thf('3', plain,
% 0.20/0.55      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.20/0.55         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.55  thf('4', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         (((k3_xboole_0 @ X1 @ X0)
% 0.20/0.55            = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.20/0.55          | (r2_hidden @ 
% 0.20/0.55             (sk_D @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0) @ X2) @ 
% 0.20/0.55             X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['1', '3'])).
% 0.20/0.55  thf('5', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.20/0.55          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.55      inference('eq_fact', [status(thm)], ['0'])).
% 0.20/0.55  thf('6', plain,
% 0.20/0.55      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.20/0.55         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.20/0.55          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.20/0.55          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.20/0.55          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.20/0.55      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.20/0.55  thf('7', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 0.20/0.55          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.20/0.55          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.20/0.55          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.55  thf('8', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.20/0.55          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.20/0.55          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.55  thf('9', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.20/0.55          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.55      inference('eq_fact', [status(thm)], ['0'])).
% 0.20/0.55  thf('10', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 0.20/0.55          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 0.20/0.55      inference('clc', [status(thm)], ['8', '9'])).
% 0.20/0.55  thf('11', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (((k3_xboole_0 @ X1 @ X0)
% 0.20/0.55            = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 0.20/0.55          | ((k3_xboole_0 @ X1 @ X0)
% 0.20/0.55              = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['4', '10'])).
% 0.20/0.55  thf('12', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((k3_xboole_0 @ X1 @ X0)
% 0.20/0.55           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.55  thf(t48_xboole_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.55  thf('13', plain,
% 0.20/0.55      (![X11 : $i, X12 : $i]:
% 0.20/0.55         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.20/0.55           = (k3_xboole_0 @ X11 @ X12))),
% 0.20/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.55  thf(t36_xboole_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.55  thf('14', plain,
% 0.20/0.55      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 0.20/0.55      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.20/0.55  thf('15', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.20/0.55      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.55  thf(t31_relat_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ A ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( v1_relat_1 @ B ) =>
% 0.20/0.55           ( ( r1_tarski @ A @ B ) =>
% 0.20/0.55             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 0.20/0.55  thf('16', plain,
% 0.20/0.55      (![X15 : $i, X16 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X15)
% 0.20/0.55          | (r1_tarski @ (k3_relat_1 @ X16) @ (k3_relat_1 @ X15))
% 0.20/0.55          | ~ (r1_tarski @ X16 @ X15)
% 0.20/0.55          | ~ (v1_relat_1 @ X16))),
% 0.20/0.55      inference('cnf', [status(esa)], [t31_relat_1])).
% 0.20/0.55  thf('17', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 0.20/0.55          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.20/0.55             (k3_relat_1 @ X0))
% 0.20/0.55          | ~ (v1_relat_1 @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.55  thf('18', plain,
% 0.20/0.55      (![X11 : $i, X12 : $i]:
% 0.20/0.55         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.20/0.55           = (k3_xboole_0 @ X11 @ X12))),
% 0.20/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.55  thf(fc2_relat_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.55  thf('19', plain,
% 0.20/0.55      (![X13 : $i, X14 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X13) | (v1_relat_1 @ (k4_xboole_0 @ X13 @ X14)))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc2_relat_1])).
% 0.20/0.55  thf('20', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((v1_relat_1 @ (k3_xboole_0 @ X1 @ X0)) | ~ (v1_relat_1 @ X1))),
% 0.20/0.55      inference('sup+', [status(thm)], ['18', '19'])).
% 0.20/0.55  thf('21', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X0)
% 0.20/0.55          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.20/0.55             (k3_relat_1 @ X0)))),
% 0.20/0.55      inference('clc', [status(thm)], ['17', '20'])).
% 0.20/0.55  thf('22', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.20/0.55           (k3_relat_1 @ X0))
% 0.20/0.55          | ~ (v1_relat_1 @ X0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['12', '21'])).
% 0.20/0.55  thf('23', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X0)
% 0.20/0.55          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.20/0.55             (k3_relat_1 @ X0)))),
% 0.20/0.55      inference('clc', [status(thm)], ['17', '20'])).
% 0.20/0.55  thf(t19_xboole_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.20/0.55       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.20/0.55  thf('24', plain,
% 0.20/0.55      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.55         (~ (r1_tarski @ X6 @ X7)
% 0.20/0.55          | ~ (r1_tarski @ X6 @ X8)
% 0.20/0.55          | (r1_tarski @ X6 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.20/0.55  thf('25', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X0)
% 0.20/0.55          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.20/0.55             (k3_xboole_0 @ (k3_relat_1 @ X0) @ X2))
% 0.20/0.55          | ~ (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X2))),
% 0.20/0.55      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.55  thf('26', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X0)
% 0.20/0.55          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.20/0.55             (k3_xboole_0 @ (k3_relat_1 @ X1) @ (k3_relat_1 @ X0)))
% 0.20/0.55          | ~ (v1_relat_1 @ X1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['22', '25'])).
% 0.20/0.55  thf(t34_relat_1, conjecture,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ A ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( v1_relat_1 @ B ) =>
% 0.20/0.55           ( r1_tarski @
% 0.20/0.55             ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.20/0.55             ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i]:
% 0.20/0.55        ( ( v1_relat_1 @ A ) =>
% 0.20/0.55          ( ![B:$i]:
% 0.20/0.55            ( ( v1_relat_1 @ B ) =>
% 0.20/0.55              ( r1_tarski @
% 0.20/0.55                ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.20/0.55                ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t34_relat_1])).
% 0.20/0.55  thf('27', plain,
% 0.20/0.55      (~ (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 0.20/0.55          (k3_xboole_0 @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('28', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.55  thf('29', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('31', plain, ($false),
% 0.20/0.55      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
