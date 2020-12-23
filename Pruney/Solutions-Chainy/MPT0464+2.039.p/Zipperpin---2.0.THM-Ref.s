%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CF0ej2BhXd

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:13 EST 2020

% Result     : Theorem 45.17s
% Output     : Refutation 45.17s
% Verified   : 
% Statistics : Number of formulae       :   53 (  80 expanded)
%              Number of leaves         :   17 (  30 expanded)
%              Depth                    :   12
%              Number of atoms          :  513 ( 859 expanded)
%              Number of equality atoms :   18 (  29 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

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

thf(fc2_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( v1_relat_1 @ ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('17',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t48_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( r1_tarski @ A @ B )
               => ( r1_tarski @ ( k5_relat_1 @ C @ A ) @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( r1_tarski @ X16 @ X15 )
      | ( r1_tarski @ ( k5_relat_1 @ X17 @ X16 ) @ ( k5_relat_1 @ X17 @ X15 ) )
      | ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['12','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('25',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X6 @ X8 )
      | ( r1_tarski @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ~ ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf(t52_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( r1_tarski @ ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ! [C: $i] :
                ( ( v1_relat_1 @ C )
               => ( r1_tarski @ ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_relat_1])).

thf('29',plain,(
    ~ ( r1_tarski @ ( k5_relat_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['30','31','32','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CF0ej2BhXd
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:31:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 45.17/45.40  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 45.17/45.40  % Solved by: fo/fo7.sh
% 45.17/45.40  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 45.17/45.40  % done 15420 iterations in 44.945s
% 45.17/45.40  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 45.17/45.40  % SZS output start Refutation
% 45.17/45.40  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 45.17/45.40  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 45.17/45.40  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 45.17/45.40  thf(sk_B_type, type, sk_B: $i).
% 45.17/45.40  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 45.17/45.40  thf(sk_A_type, type, sk_A: $i).
% 45.17/45.40  thf(sk_C_type, type, sk_C: $i).
% 45.17/45.40  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 45.17/45.40  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 45.17/45.40  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 45.17/45.40  thf(d4_xboole_0, axiom,
% 45.17/45.40    (![A:$i,B:$i,C:$i]:
% 45.17/45.40     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 45.17/45.40       ( ![D:$i]:
% 45.17/45.40         ( ( r2_hidden @ D @ C ) <=>
% 45.17/45.40           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 45.17/45.40  thf('0', plain,
% 45.17/45.40      (![X1 : $i, X2 : $i, X5 : $i]:
% 45.17/45.40         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 45.17/45.40          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 45.17/45.40          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 45.17/45.40      inference('cnf', [status(esa)], [d4_xboole_0])).
% 45.17/45.40  thf('1', plain,
% 45.17/45.40      (![X0 : $i, X1 : $i]:
% 45.17/45.40         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 45.17/45.40          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 45.17/45.40      inference('eq_fact', [status(thm)], ['0'])).
% 45.17/45.40  thf('2', plain,
% 45.17/45.40      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 45.17/45.40         (~ (r2_hidden @ X4 @ X3)
% 45.17/45.40          | (r2_hidden @ X4 @ X2)
% 45.17/45.40          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 45.17/45.40      inference('cnf', [status(esa)], [d4_xboole_0])).
% 45.17/45.40  thf('3', plain,
% 45.17/45.40      (![X1 : $i, X2 : $i, X4 : $i]:
% 45.17/45.40         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 45.17/45.40      inference('simplify', [status(thm)], ['2'])).
% 45.17/45.40  thf('4', plain,
% 45.17/45.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.17/45.40         (((k3_xboole_0 @ X1 @ X0)
% 45.17/45.40            = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 45.17/45.40          | (r2_hidden @ 
% 45.17/45.40             (sk_D @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0) @ X2) @ 
% 45.17/45.40             X0))),
% 45.17/45.40      inference('sup-', [status(thm)], ['1', '3'])).
% 45.17/45.40  thf('5', plain,
% 45.17/45.40      (![X0 : $i, X1 : $i]:
% 45.17/45.40         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 45.17/45.40          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 45.17/45.40      inference('eq_fact', [status(thm)], ['0'])).
% 45.17/45.40  thf('6', plain,
% 45.17/45.40      (![X1 : $i, X2 : $i, X5 : $i]:
% 45.17/45.40         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 45.17/45.40          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 45.17/45.40          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 45.17/45.40          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 45.17/45.40      inference('cnf', [status(esa)], [d4_xboole_0])).
% 45.17/45.40  thf('7', plain,
% 45.17/45.40      (![X0 : $i, X1 : $i]:
% 45.17/45.40         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 45.17/45.40          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 45.17/45.40          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 45.17/45.40          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 45.17/45.40      inference('sup-', [status(thm)], ['5', '6'])).
% 45.17/45.40  thf('8', plain,
% 45.17/45.40      (![X0 : $i, X1 : $i]:
% 45.17/45.40         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 45.17/45.40          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 45.17/45.40          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 45.17/45.40      inference('simplify', [status(thm)], ['7'])).
% 45.17/45.40  thf('9', plain,
% 45.17/45.40      (![X0 : $i, X1 : $i]:
% 45.17/45.40         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 45.17/45.40          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 45.17/45.40      inference('eq_fact', [status(thm)], ['0'])).
% 45.17/45.40  thf('10', plain,
% 45.17/45.40      (![X0 : $i, X1 : $i]:
% 45.17/45.40         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 45.17/45.40          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 45.17/45.40      inference('clc', [status(thm)], ['8', '9'])).
% 45.17/45.40  thf('11', plain,
% 45.17/45.40      (![X0 : $i, X1 : $i]:
% 45.17/45.40         (((k3_xboole_0 @ X1 @ X0)
% 45.17/45.40            = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 45.17/45.40          | ((k3_xboole_0 @ X1 @ X0)
% 45.17/45.40              = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))))),
% 45.17/45.40      inference('sup-', [status(thm)], ['4', '10'])).
% 45.17/45.40  thf('12', plain,
% 45.17/45.40      (![X0 : $i, X1 : $i]:
% 45.17/45.40         ((k3_xboole_0 @ X1 @ X0)
% 45.17/45.40           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 45.17/45.40      inference('simplify', [status(thm)], ['11'])).
% 45.17/45.40  thf(t48_xboole_1, axiom,
% 45.17/45.40    (![A:$i,B:$i]:
% 45.17/45.40     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 45.17/45.40  thf('13', plain,
% 45.17/45.40      (![X11 : $i, X12 : $i]:
% 45.17/45.40         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 45.17/45.40           = (k3_xboole_0 @ X11 @ X12))),
% 45.17/45.40      inference('cnf', [status(esa)], [t48_xboole_1])).
% 45.17/45.40  thf(fc2_relat_1, axiom,
% 45.17/45.40    (![A:$i,B:$i]:
% 45.17/45.40     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_xboole_0 @ A @ B ) ) ))).
% 45.17/45.40  thf('14', plain,
% 45.17/45.40      (![X13 : $i, X14 : $i]:
% 45.17/45.40         (~ (v1_relat_1 @ X13) | (v1_relat_1 @ (k4_xboole_0 @ X13 @ X14)))),
% 45.17/45.40      inference('cnf', [status(esa)], [fc2_relat_1])).
% 45.17/45.40  thf('15', plain,
% 45.17/45.40      (![X0 : $i, X1 : $i]:
% 45.17/45.40         ((v1_relat_1 @ (k3_xboole_0 @ X1 @ X0)) | ~ (v1_relat_1 @ X1))),
% 45.17/45.40      inference('sup+', [status(thm)], ['13', '14'])).
% 45.17/45.40  thf('16', plain,
% 45.17/45.40      (![X11 : $i, X12 : $i]:
% 45.17/45.40         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 45.17/45.40           = (k3_xboole_0 @ X11 @ X12))),
% 45.17/45.40      inference('cnf', [status(esa)], [t48_xboole_1])).
% 45.17/45.40  thf(t36_xboole_1, axiom,
% 45.17/45.40    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 45.17/45.40  thf('17', plain,
% 45.17/45.40      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 45.17/45.40      inference('cnf', [status(esa)], [t36_xboole_1])).
% 45.17/45.40  thf('18', plain,
% 45.17/45.40      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 45.17/45.40      inference('sup+', [status(thm)], ['16', '17'])).
% 45.17/45.40  thf(t48_relat_1, axiom,
% 45.17/45.40    (![A:$i]:
% 45.17/45.40     ( ( v1_relat_1 @ A ) =>
% 45.17/45.40       ( ![B:$i]:
% 45.17/45.40         ( ( v1_relat_1 @ B ) =>
% 45.17/45.40           ( ![C:$i]:
% 45.17/45.40             ( ( v1_relat_1 @ C ) =>
% 45.17/45.40               ( ( r1_tarski @ A @ B ) =>
% 45.17/45.40                 ( r1_tarski @ ( k5_relat_1 @ C @ A ) @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) ) ))).
% 45.17/45.40  thf('19', plain,
% 45.17/45.40      (![X15 : $i, X16 : $i, X17 : $i]:
% 45.17/45.40         (~ (v1_relat_1 @ X15)
% 45.17/45.40          | ~ (r1_tarski @ X16 @ X15)
% 45.17/45.40          | (r1_tarski @ (k5_relat_1 @ X17 @ X16) @ (k5_relat_1 @ X17 @ X15))
% 45.17/45.40          | ~ (v1_relat_1 @ X17)
% 45.17/45.40          | ~ (v1_relat_1 @ X16))),
% 45.17/45.40      inference('cnf', [status(esa)], [t48_relat_1])).
% 45.17/45.40  thf('20', plain,
% 45.17/45.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.17/45.40         (~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 45.17/45.40          | ~ (v1_relat_1 @ X2)
% 45.17/45.40          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 45.17/45.40             (k5_relat_1 @ X2 @ X0))
% 45.17/45.40          | ~ (v1_relat_1 @ X0))),
% 45.17/45.40      inference('sup-', [status(thm)], ['18', '19'])).
% 45.17/45.40  thf('21', plain,
% 45.17/45.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.17/45.40         (~ (v1_relat_1 @ X1)
% 45.17/45.40          | ~ (v1_relat_1 @ X1)
% 45.17/45.40          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 45.17/45.40             (k5_relat_1 @ X2 @ X1))
% 45.17/45.40          | ~ (v1_relat_1 @ X2))),
% 45.17/45.40      inference('sup-', [status(thm)], ['15', '20'])).
% 45.17/45.40  thf('22', plain,
% 45.17/45.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.17/45.40         (~ (v1_relat_1 @ X2)
% 45.17/45.40          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 45.17/45.40             (k5_relat_1 @ X2 @ X1))
% 45.17/45.40          | ~ (v1_relat_1 @ X1))),
% 45.17/45.40      inference('simplify', [status(thm)], ['21'])).
% 45.17/45.40  thf('23', plain,
% 45.17/45.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.17/45.40         ((r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 45.17/45.40           (k5_relat_1 @ X2 @ X0))
% 45.17/45.40          | ~ (v1_relat_1 @ X0)
% 45.17/45.40          | ~ (v1_relat_1 @ X2))),
% 45.17/45.40      inference('sup+', [status(thm)], ['12', '22'])).
% 45.17/45.40  thf('24', plain,
% 45.17/45.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.17/45.40         (~ (v1_relat_1 @ X2)
% 45.17/45.40          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 45.17/45.40             (k5_relat_1 @ X2 @ X1))
% 45.17/45.40          | ~ (v1_relat_1 @ X1))),
% 45.17/45.40      inference('simplify', [status(thm)], ['21'])).
% 45.17/45.40  thf(t19_xboole_1, axiom,
% 45.17/45.40    (![A:$i,B:$i,C:$i]:
% 45.17/45.40     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 45.17/45.40       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 45.17/45.40  thf('25', plain,
% 45.17/45.40      (![X6 : $i, X7 : $i, X8 : $i]:
% 45.17/45.40         (~ (r1_tarski @ X6 @ X7)
% 45.17/45.40          | ~ (r1_tarski @ X6 @ X8)
% 45.17/45.40          | (r1_tarski @ X6 @ (k3_xboole_0 @ X7 @ X8)))),
% 45.17/45.40      inference('cnf', [status(esa)], [t19_xboole_1])).
% 45.17/45.40  thf('26', plain,
% 45.17/45.40      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 45.17/45.40         (~ (v1_relat_1 @ X0)
% 45.17/45.40          | ~ (v1_relat_1 @ X1)
% 45.17/45.40          | (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ 
% 45.17/45.40             (k3_xboole_0 @ (k5_relat_1 @ X1 @ X0) @ X3))
% 45.17/45.40          | ~ (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ X3))),
% 45.17/45.40      inference('sup-', [status(thm)], ['24', '25'])).
% 45.17/45.40  thf('27', plain,
% 45.17/45.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.17/45.40         (~ (v1_relat_1 @ X1)
% 45.17/45.40          | ~ (v1_relat_1 @ X0)
% 45.17/45.40          | (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 45.17/45.40             (k3_xboole_0 @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0)))
% 45.17/45.40          | ~ (v1_relat_1 @ X1)
% 45.17/45.40          | ~ (v1_relat_1 @ X2))),
% 45.17/45.40      inference('sup-', [status(thm)], ['23', '26'])).
% 45.17/45.40  thf('28', plain,
% 45.17/45.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.17/45.40         (~ (v1_relat_1 @ X2)
% 45.17/45.40          | (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 45.17/45.40             (k3_xboole_0 @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0)))
% 45.17/45.40          | ~ (v1_relat_1 @ X0)
% 45.17/45.40          | ~ (v1_relat_1 @ X1))),
% 45.17/45.40      inference('simplify', [status(thm)], ['27'])).
% 45.17/45.40  thf(t52_relat_1, conjecture,
% 45.17/45.40    (![A:$i]:
% 45.17/45.40     ( ( v1_relat_1 @ A ) =>
% 45.17/45.40       ( ![B:$i]:
% 45.17/45.40         ( ( v1_relat_1 @ B ) =>
% 45.17/45.40           ( ![C:$i]:
% 45.17/45.40             ( ( v1_relat_1 @ C ) =>
% 45.17/45.40               ( r1_tarski @
% 45.17/45.40                 ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 45.17/45.40                 ( k3_xboole_0 @
% 45.17/45.40                   ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ))).
% 45.17/45.40  thf(zf_stmt_0, negated_conjecture,
% 45.17/45.40    (~( ![A:$i]:
% 45.17/45.40        ( ( v1_relat_1 @ A ) =>
% 45.17/45.40          ( ![B:$i]:
% 45.17/45.40            ( ( v1_relat_1 @ B ) =>
% 45.17/45.40              ( ![C:$i]:
% 45.17/45.40                ( ( v1_relat_1 @ C ) =>
% 45.17/45.40                  ( r1_tarski @
% 45.17/45.40                    ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 45.17/45.40                    ( k3_xboole_0 @
% 45.17/45.40                      ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ) )),
% 45.17/45.40    inference('cnf.neg', [status(esa)], [t52_relat_1])).
% 45.17/45.40  thf('29', plain,
% 45.17/45.40      (~ (r1_tarski @ (k5_relat_1 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 45.17/45.40          (k3_xboole_0 @ (k5_relat_1 @ sk_A @ sk_B) @ 
% 45.17/45.40           (k5_relat_1 @ sk_A @ sk_C)))),
% 45.17/45.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.17/45.40  thf('30', plain,
% 45.17/45.40      ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_C) | ~ (v1_relat_1 @ sk_B))),
% 45.17/45.40      inference('sup-', [status(thm)], ['28', '29'])).
% 45.17/45.40  thf('31', plain, ((v1_relat_1 @ sk_A)),
% 45.17/45.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.17/45.40  thf('32', plain, ((v1_relat_1 @ sk_C)),
% 45.17/45.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.17/45.40  thf('33', plain, ((v1_relat_1 @ sk_B)),
% 45.17/45.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.17/45.40  thf('34', plain, ($false),
% 45.17/45.40      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 45.17/45.40  
% 45.17/45.40  % SZS output end Refutation
% 45.17/45.40  
% 45.17/45.40  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
