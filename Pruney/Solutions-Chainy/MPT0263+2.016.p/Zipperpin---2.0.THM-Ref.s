%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HXqGrKtLmL

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:33 EST 2020

% Result     : Theorem 3.30s
% Output     : Refutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :   47 (  67 expanded)
%              Number of leaves         :   14 (  23 expanded)
%              Depth                    :   13
%              Number of atoms          :  418 ( 721 expanded)
%              Number of equality atoms :   39 (  60 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ( X16 = X13 )
      | ( X15
       != ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('3',plain,(
    ! [X13: $i,X16: $i] :
      ( ( X16 = X13 )
      | ~ ( r2_hidden @ X16 @ ( k1_tarski @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('6',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['4','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('15',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('16',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('20',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_xboole_0 @ X10 @ X12 )
      | ( ( k4_xboole_0 @ X10 @ X12 )
       != X10 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
       != ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','22'])).

thf(t58_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
      | ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
        | ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t58_zfmisc_1])).

thf('24',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['23','24'])).

thf(l31_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('26',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_xboole_0 @ X25 @ ( k1_tarski @ X24 ) )
        = ( k1_tarski @ X24 ) )
      | ~ ( r2_hidden @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('27',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('30',plain,(
    ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['27','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HXqGrKtLmL
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:57:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 3.30/3.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.30/3.51  % Solved by: fo/fo7.sh
% 3.30/3.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.30/3.51  % done 2250 iterations in 3.031s
% 3.30/3.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.30/3.51  % SZS output start Refutation
% 3.30/3.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.30/3.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 3.30/3.51  thf(sk_A_type, type, sk_A: $i).
% 3.30/3.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.30/3.51  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 3.30/3.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.30/3.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.30/3.51  thf(sk_B_type, type, sk_B: $i).
% 3.30/3.51  thf(d5_xboole_0, axiom,
% 3.30/3.51    (![A:$i,B:$i,C:$i]:
% 3.30/3.51     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 3.30/3.51       ( ![D:$i]:
% 3.30/3.51         ( ( r2_hidden @ D @ C ) <=>
% 3.30/3.51           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 3.30/3.51  thf('0', plain,
% 3.30/3.51      (![X3 : $i, X4 : $i, X7 : $i]:
% 3.30/3.51         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 3.30/3.51          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 3.30/3.51          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 3.30/3.51      inference('cnf', [status(esa)], [d5_xboole_0])).
% 3.30/3.51  thf('1', plain,
% 3.30/3.51      (![X0 : $i, X1 : $i]:
% 3.30/3.51         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 3.30/3.51          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 3.30/3.51      inference('eq_fact', [status(thm)], ['0'])).
% 3.30/3.51  thf(d1_tarski, axiom,
% 3.30/3.51    (![A:$i,B:$i]:
% 3.30/3.51     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 3.30/3.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 3.30/3.51  thf('2', plain,
% 3.30/3.51      (![X13 : $i, X15 : $i, X16 : $i]:
% 3.30/3.51         (~ (r2_hidden @ X16 @ X15)
% 3.30/3.51          | ((X16) = (X13))
% 3.30/3.51          | ((X15) != (k1_tarski @ X13)))),
% 3.30/3.51      inference('cnf', [status(esa)], [d1_tarski])).
% 3.30/3.51  thf('3', plain,
% 3.30/3.51      (![X13 : $i, X16 : $i]:
% 3.30/3.51         (((X16) = (X13)) | ~ (r2_hidden @ X16 @ (k1_tarski @ X13)))),
% 3.30/3.51      inference('simplify', [status(thm)], ['2'])).
% 3.30/3.51  thf('4', plain,
% 3.30/3.51      (![X0 : $i, X1 : $i]:
% 3.30/3.51         (((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 3.30/3.51          | ((sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 3.30/3.51      inference('sup-', [status(thm)], ['1', '3'])).
% 3.30/3.51  thf('5', plain,
% 3.30/3.51      (![X0 : $i, X1 : $i]:
% 3.30/3.51         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 3.30/3.51          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 3.30/3.51      inference('eq_fact', [status(thm)], ['0'])).
% 3.30/3.51  thf('6', plain,
% 3.30/3.51      (![X3 : $i, X4 : $i, X7 : $i]:
% 3.30/3.51         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 3.30/3.51          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 3.30/3.51          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 3.30/3.51          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 3.30/3.51      inference('cnf', [status(esa)], [d5_xboole_0])).
% 3.30/3.51  thf('7', plain,
% 3.30/3.51      (![X0 : $i, X1 : $i]:
% 3.30/3.51         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 3.30/3.51          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 3.30/3.51          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 3.30/3.51          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 3.30/3.51      inference('sup-', [status(thm)], ['5', '6'])).
% 3.30/3.51  thf('8', plain,
% 3.30/3.51      (![X0 : $i, X1 : $i]:
% 3.30/3.51         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 3.30/3.51          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 3.30/3.51          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 3.30/3.51      inference('simplify', [status(thm)], ['7'])).
% 3.30/3.51  thf('9', plain,
% 3.30/3.51      (![X0 : $i, X1 : $i]:
% 3.30/3.51         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 3.30/3.51          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 3.30/3.51      inference('eq_fact', [status(thm)], ['0'])).
% 3.30/3.51  thf('10', plain,
% 3.30/3.51      (![X0 : $i, X1 : $i]:
% 3.30/3.51         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 3.30/3.51          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 3.30/3.51      inference('clc', [status(thm)], ['8', '9'])).
% 3.30/3.51  thf('11', plain,
% 3.30/3.51      (![X0 : $i, X1 : $i]:
% 3.30/3.51         ((r2_hidden @ X0 @ X1)
% 3.30/3.51          | ((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 3.30/3.51          | ((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 3.30/3.51      inference('sup+', [status(thm)], ['4', '10'])).
% 3.30/3.51  thf('12', plain,
% 3.30/3.51      (![X0 : $i, X1 : $i]:
% 3.30/3.51         (((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 3.30/3.51          | (r2_hidden @ X0 @ X1))),
% 3.30/3.51      inference('simplify', [status(thm)], ['11'])).
% 3.30/3.51  thf('13', plain,
% 3.30/3.51      (![X0 : $i, X1 : $i]:
% 3.30/3.51         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 3.30/3.51          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 3.30/3.51      inference('clc', [status(thm)], ['8', '9'])).
% 3.30/3.51  thf('14', plain,
% 3.30/3.51      (![X0 : $i, X1 : $i]:
% 3.30/3.51         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 3.30/3.51          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 3.30/3.51      inference('eq_fact', [status(thm)], ['0'])).
% 3.30/3.51  thf('15', plain,
% 3.30/3.51      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 3.30/3.51         (~ (r2_hidden @ X6 @ X5)
% 3.30/3.51          | ~ (r2_hidden @ X6 @ X4)
% 3.30/3.51          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 3.30/3.51      inference('cnf', [status(esa)], [d5_xboole_0])).
% 3.30/3.51  thf('16', plain,
% 3.30/3.51      (![X3 : $i, X4 : $i, X6 : $i]:
% 3.30/3.51         (~ (r2_hidden @ X6 @ X4)
% 3.30/3.51          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 3.30/3.51      inference('simplify', [status(thm)], ['15'])).
% 3.30/3.51  thf('17', plain,
% 3.30/3.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.30/3.51         (((k4_xboole_0 @ X1 @ X0)
% 3.30/3.51            = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))
% 3.30/3.51          | ~ (r2_hidden @ 
% 3.30/3.51               (sk_D @ (k4_xboole_0 @ X1 @ X0) @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 3.30/3.51               X0))),
% 3.30/3.51      inference('sup-', [status(thm)], ['14', '16'])).
% 3.30/3.51  thf('18', plain,
% 3.30/3.51      (![X0 : $i, X1 : $i]:
% 3.30/3.51         (((k4_xboole_0 @ X1 @ X0)
% 3.30/3.51            = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))
% 3.30/3.51          | ((k4_xboole_0 @ X1 @ X0)
% 3.30/3.51              = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)))),
% 3.30/3.51      inference('sup-', [status(thm)], ['13', '17'])).
% 3.30/3.51  thf('19', plain,
% 3.30/3.51      (![X0 : $i, X1 : $i]:
% 3.30/3.51         ((k4_xboole_0 @ X1 @ X0)
% 3.30/3.51           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 3.30/3.51      inference('simplify', [status(thm)], ['18'])).
% 3.30/3.51  thf(t83_xboole_1, axiom,
% 3.30/3.51    (![A:$i,B:$i]:
% 3.30/3.51     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 3.30/3.51  thf('20', plain,
% 3.30/3.51      (![X10 : $i, X12 : $i]:
% 3.30/3.51         ((r1_xboole_0 @ X10 @ X12) | ((k4_xboole_0 @ X10 @ X12) != (X10)))),
% 3.30/3.51      inference('cnf', [status(esa)], [t83_xboole_1])).
% 3.30/3.51  thf('21', plain,
% 3.30/3.51      (![X0 : $i, X1 : $i]:
% 3.30/3.51         (((k4_xboole_0 @ X1 @ X0) != (k4_xboole_0 @ X1 @ X0))
% 3.30/3.51          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 3.30/3.51      inference('sup-', [status(thm)], ['19', '20'])).
% 3.30/3.51  thf('22', plain,
% 3.30/3.51      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 3.30/3.51      inference('simplify', [status(thm)], ['21'])).
% 3.30/3.51  thf('23', plain,
% 3.30/3.51      (![X0 : $i, X1 : $i]:
% 3.30/3.51         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 3.30/3.51      inference('sup+', [status(thm)], ['12', '22'])).
% 3.30/3.51  thf(t58_zfmisc_1, conjecture,
% 3.30/3.51    (![A:$i,B:$i]:
% 3.30/3.51     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 3.30/3.51       ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 3.30/3.51  thf(zf_stmt_0, negated_conjecture,
% 3.30/3.51    (~( ![A:$i,B:$i]:
% 3.30/3.51        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 3.30/3.51          ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )),
% 3.30/3.51    inference('cnf.neg', [status(esa)], [t58_zfmisc_1])).
% 3.30/3.51  thf('24', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)),
% 3.30/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.51  thf('25', plain, ((r2_hidden @ sk_A @ sk_B)),
% 3.30/3.51      inference('sup-', [status(thm)], ['23', '24'])).
% 3.30/3.51  thf(l31_zfmisc_1, axiom,
% 3.30/3.51    (![A:$i,B:$i]:
% 3.30/3.51     ( ( r2_hidden @ A @ B ) =>
% 3.30/3.51       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 3.30/3.51  thf('26', plain,
% 3.30/3.51      (![X24 : $i, X25 : $i]:
% 3.30/3.51         (((k3_xboole_0 @ X25 @ (k1_tarski @ X24)) = (k1_tarski @ X24))
% 3.30/3.51          | ~ (r2_hidden @ X24 @ X25))),
% 3.30/3.51      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 3.30/3.51  thf('27', plain,
% 3.30/3.51      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 3.30/3.51      inference('sup-', [status(thm)], ['25', '26'])).
% 3.30/3.51  thf('28', plain,
% 3.30/3.51      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 3.30/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.51  thf(commutativity_k3_xboole_0, axiom,
% 3.30/3.51    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 3.30/3.51  thf('29', plain,
% 3.30/3.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.30/3.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.30/3.51  thf('30', plain,
% 3.30/3.51      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (k1_tarski @ sk_A))),
% 3.30/3.51      inference('demod', [status(thm)], ['28', '29'])).
% 3.30/3.51  thf('31', plain, ($false),
% 3.30/3.51      inference('simplify_reflect-', [status(thm)], ['27', '30'])).
% 3.30/3.51  
% 3.30/3.51  % SZS output end Refutation
% 3.30/3.51  
% 3.30/3.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
