%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IVy3i0GQbK

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:32 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   52 (  67 expanded)
%              Number of leaves         :   13 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :  442 ( 643 expanded)
%              Number of equality atoms :   32 (  46 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('2',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('4',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X17 @ X16 )
      | ( X17 = X14 )
      | ( X16
       != ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('5',plain,(
    ! [X14: $i,X17: $i] :
      ( ( X17 = X14 )
      | ~ ( r2_hidden @ X17 @ ( k1_tarski @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('8',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('9',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('15',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

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

thf('19',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['21'])).

thf('23',plain,(
    ! [X14: $i,X17: $i] :
      ( ( X17 = X14 )
      | ~ ( r2_hidden @ X17 @ ( k1_tarski @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['21'])).

thf('26',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['21'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','32'])).

thf('34',plain,(
    ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('36',plain,(
    ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['33','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IVy3i0GQbK
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:01:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.49/1.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.49/1.71  % Solved by: fo/fo7.sh
% 1.49/1.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.49/1.71  % done 2845 iterations in 1.243s
% 1.49/1.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.49/1.71  % SZS output start Refutation
% 1.49/1.71  thf(sk_A_type, type, sk_A: $i).
% 1.49/1.71  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.49/1.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.49/1.71  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.49/1.71  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.49/1.71  thf(sk_B_type, type, sk_B: $i).
% 1.49/1.71  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.49/1.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.49/1.71  thf(t4_xboole_0, axiom,
% 1.49/1.71    (![A:$i,B:$i]:
% 1.49/1.71     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.49/1.71            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.49/1.71       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.49/1.71            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.49/1.71  thf('0', plain,
% 1.49/1.71      (![X8 : $i, X9 : $i]:
% 1.49/1.71         ((r1_xboole_0 @ X8 @ X9)
% 1.49/1.71          | (r2_hidden @ (sk_C @ X9 @ X8) @ (k3_xboole_0 @ X8 @ X9)))),
% 1.49/1.71      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.49/1.71  thf(d4_xboole_0, axiom,
% 1.49/1.71    (![A:$i,B:$i,C:$i]:
% 1.49/1.71     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 1.49/1.71       ( ![D:$i]:
% 1.49/1.71         ( ( r2_hidden @ D @ C ) <=>
% 1.49/1.71           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.49/1.71  thf('1', plain,
% 1.49/1.71      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.49/1.71         (~ (r2_hidden @ X6 @ X5)
% 1.49/1.71          | (r2_hidden @ X6 @ X4)
% 1.49/1.71          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 1.49/1.71      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.49/1.71  thf('2', plain,
% 1.49/1.71      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.49/1.71         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 1.49/1.71      inference('simplify', [status(thm)], ['1'])).
% 1.49/1.71  thf('3', plain,
% 1.49/1.71      (![X0 : $i, X1 : $i]:
% 1.49/1.71         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C @ X0 @ X1) @ X0))),
% 1.49/1.71      inference('sup-', [status(thm)], ['0', '2'])).
% 1.49/1.71  thf(d1_tarski, axiom,
% 1.49/1.71    (![A:$i,B:$i]:
% 1.49/1.71     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.49/1.71       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.49/1.71  thf('4', plain,
% 1.49/1.71      (![X14 : $i, X16 : $i, X17 : $i]:
% 1.49/1.71         (~ (r2_hidden @ X17 @ X16)
% 1.49/1.71          | ((X17) = (X14))
% 1.49/1.71          | ((X16) != (k1_tarski @ X14)))),
% 1.49/1.71      inference('cnf', [status(esa)], [d1_tarski])).
% 1.49/1.71  thf('5', plain,
% 1.49/1.71      (![X14 : $i, X17 : $i]:
% 1.49/1.71         (((X17) = (X14)) | ~ (r2_hidden @ X17 @ (k1_tarski @ X14)))),
% 1.49/1.71      inference('simplify', [status(thm)], ['4'])).
% 1.49/1.71  thf('6', plain,
% 1.49/1.71      (![X0 : $i, X1 : $i]:
% 1.49/1.71         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 1.49/1.71          | ((sk_C @ (k1_tarski @ X0) @ X1) = (X0)))),
% 1.49/1.71      inference('sup-', [status(thm)], ['3', '5'])).
% 1.49/1.71  thf('7', plain,
% 1.49/1.71      (![X8 : $i, X9 : $i]:
% 1.49/1.71         ((r1_xboole_0 @ X8 @ X9)
% 1.49/1.71          | (r2_hidden @ (sk_C @ X9 @ X8) @ (k3_xboole_0 @ X8 @ X9)))),
% 1.49/1.71      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.49/1.71  thf('8', plain,
% 1.49/1.71      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.49/1.71         (~ (r2_hidden @ X6 @ X5)
% 1.49/1.71          | (r2_hidden @ X6 @ X3)
% 1.49/1.71          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 1.49/1.71      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.49/1.71  thf('9', plain,
% 1.49/1.71      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.49/1.71         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 1.49/1.71      inference('simplify', [status(thm)], ['8'])).
% 1.49/1.71  thf('10', plain,
% 1.49/1.71      (![X0 : $i, X1 : $i]:
% 1.49/1.71         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 1.49/1.71      inference('sup-', [status(thm)], ['7', '9'])).
% 1.49/1.71  thf('11', plain,
% 1.49/1.71      (![X0 : $i, X1 : $i]:
% 1.49/1.71         ((r2_hidden @ X0 @ X1)
% 1.49/1.71          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 1.49/1.71          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 1.49/1.71      inference('sup+', [status(thm)], ['6', '10'])).
% 1.49/1.71  thf('12', plain,
% 1.49/1.71      (![X0 : $i, X1 : $i]:
% 1.49/1.71         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0)) | (r2_hidden @ X0 @ X1))),
% 1.49/1.71      inference('simplify', [status(thm)], ['11'])).
% 1.49/1.71  thf('13', plain,
% 1.49/1.71      (![X8 : $i, X9 : $i]:
% 1.49/1.71         ((r1_xboole_0 @ X8 @ X9)
% 1.49/1.71          | (r2_hidden @ (sk_C @ X9 @ X8) @ (k3_xboole_0 @ X8 @ X9)))),
% 1.49/1.71      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.49/1.71  thf(commutativity_k3_xboole_0, axiom,
% 1.49/1.71    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.49/1.71  thf('14', plain,
% 1.49/1.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.49/1.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.49/1.71  thf('15', plain,
% 1.49/1.71      (![X8 : $i, X10 : $i, X11 : $i]:
% 1.49/1.71         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 1.49/1.71          | ~ (r1_xboole_0 @ X8 @ X11))),
% 1.49/1.71      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.49/1.71  thf('16', plain,
% 1.49/1.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.49/1.71         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.49/1.71          | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.49/1.71      inference('sup-', [status(thm)], ['14', '15'])).
% 1.49/1.71  thf('17', plain,
% 1.49/1.71      (![X0 : $i, X1 : $i]:
% 1.49/1.71         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.49/1.71      inference('sup-', [status(thm)], ['13', '16'])).
% 1.49/1.71  thf('18', plain,
% 1.49/1.71      (![X0 : $i, X1 : $i]:
% 1.49/1.71         ((r2_hidden @ X0 @ X1) | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 1.49/1.71      inference('sup-', [status(thm)], ['12', '17'])).
% 1.49/1.71  thf(t58_zfmisc_1, conjecture,
% 1.49/1.71    (![A:$i,B:$i]:
% 1.49/1.71     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 1.49/1.71       ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 1.49/1.71  thf(zf_stmt_0, negated_conjecture,
% 1.49/1.71    (~( ![A:$i,B:$i]:
% 1.49/1.71        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 1.49/1.71          ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )),
% 1.49/1.71    inference('cnf.neg', [status(esa)], [t58_zfmisc_1])).
% 1.49/1.71  thf('19', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)),
% 1.49/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.71  thf('20', plain, ((r2_hidden @ sk_A @ sk_B)),
% 1.49/1.71      inference('sup-', [status(thm)], ['18', '19'])).
% 1.49/1.71  thf('21', plain,
% 1.49/1.71      (![X3 : $i, X4 : $i, X7 : $i]:
% 1.49/1.71         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 1.49/1.71          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 1.49/1.71          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 1.49/1.71      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.49/1.71  thf('22', plain,
% 1.49/1.71      (![X0 : $i, X1 : $i]:
% 1.49/1.71         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.49/1.71          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.49/1.71      inference('eq_fact', [status(thm)], ['21'])).
% 1.49/1.71  thf('23', plain,
% 1.49/1.71      (![X14 : $i, X17 : $i]:
% 1.49/1.71         (((X17) = (X14)) | ~ (r2_hidden @ X17 @ (k1_tarski @ X14)))),
% 1.49/1.71      inference('simplify', [status(thm)], ['4'])).
% 1.49/1.71  thf('24', plain,
% 1.49/1.71      (![X0 : $i, X1 : $i]:
% 1.49/1.71         (((k1_tarski @ X0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 1.49/1.71          | ((sk_D @ (k1_tarski @ X0) @ (k1_tarski @ X0) @ X1) = (X0)))),
% 1.49/1.71      inference('sup-', [status(thm)], ['22', '23'])).
% 1.49/1.71  thf('25', plain,
% 1.49/1.71      (![X0 : $i, X1 : $i]:
% 1.49/1.71         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.49/1.71          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.49/1.71      inference('eq_fact', [status(thm)], ['21'])).
% 1.49/1.71  thf('26', plain,
% 1.49/1.71      (![X3 : $i, X4 : $i, X7 : $i]:
% 1.49/1.71         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 1.49/1.71          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 1.49/1.71          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 1.49/1.71          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 1.49/1.71      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.49/1.71  thf('27', plain,
% 1.49/1.71      (![X0 : $i, X1 : $i]:
% 1.49/1.71         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 1.49/1.71          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.49/1.71          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 1.49/1.71          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.49/1.71      inference('sup-', [status(thm)], ['25', '26'])).
% 1.49/1.71  thf('28', plain,
% 1.49/1.71      (![X0 : $i, X1 : $i]:
% 1.49/1.71         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 1.49/1.71          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.49/1.71          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.49/1.71      inference('simplify', [status(thm)], ['27'])).
% 1.49/1.71  thf('29', plain,
% 1.49/1.71      (![X0 : $i, X1 : $i]:
% 1.49/1.71         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.49/1.71          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.49/1.71      inference('eq_fact', [status(thm)], ['21'])).
% 1.49/1.71  thf('30', plain,
% 1.49/1.71      (![X0 : $i, X1 : $i]:
% 1.49/1.71         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 1.49/1.71          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 1.49/1.71      inference('clc', [status(thm)], ['28', '29'])).
% 1.49/1.71  thf('31', plain,
% 1.49/1.71      (![X0 : $i, X1 : $i]:
% 1.49/1.71         (~ (r2_hidden @ X0 @ X1)
% 1.49/1.71          | ((k1_tarski @ X0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 1.49/1.71          | ((k1_tarski @ X0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 1.49/1.71      inference('sup-', [status(thm)], ['24', '30'])).
% 1.49/1.71  thf('32', plain,
% 1.49/1.71      (![X0 : $i, X1 : $i]:
% 1.49/1.71         (((k1_tarski @ X0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 1.49/1.71          | ~ (r2_hidden @ X0 @ X1))),
% 1.49/1.71      inference('simplify', [status(thm)], ['31'])).
% 1.49/1.71  thf('33', plain,
% 1.49/1.71      (((k1_tarski @ sk_A) = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 1.49/1.71      inference('sup-', [status(thm)], ['20', '32'])).
% 1.49/1.71  thf('34', plain,
% 1.49/1.71      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 1.49/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.71  thf('35', plain,
% 1.49/1.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.49/1.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.49/1.71  thf('36', plain,
% 1.49/1.71      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (k1_tarski @ sk_A))),
% 1.49/1.71      inference('demod', [status(thm)], ['34', '35'])).
% 1.49/1.71  thf('37', plain, ($false),
% 1.49/1.71      inference('simplify_reflect-', [status(thm)], ['33', '36'])).
% 1.49/1.71  
% 1.49/1.71  % SZS output end Refutation
% 1.49/1.71  
% 1.49/1.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
