%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qBNUphHEYs

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:32 EST 2020

% Result     : Theorem 3.58s
% Output     : Refutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :   54 (  78 expanded)
%              Number of leaves         :   13 (  27 expanded)
%              Depth                    :   13
%              Number of atoms          :  456 ( 774 expanded)
%              Number of equality atoms :   30 (  49 expanded)
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

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('3',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X17 @ X16 )
      | ( X17 = X14 )
      | ( X16
       != ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('4',plain,(
    ! [X14: $i,X17: $i] :
      ( ( X17 = X14 )
      | ~ ( r2_hidden @ X17 @ ( k1_tarski @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

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

thf('10',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('13',plain,(
    ! [X14: $i,X17: $i] :
      ( ( X17 = X14 )
      | ~ ( r2_hidden @ X17 @ ( k1_tarski @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('16',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ X2 @ ( k1_tarski @ X0 ) )
      | ~ ( r1_xboole_0 @ X2 @ X1 )
      | ( r1_xboole_0 @ X2 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X1 )
      | ( r1_xboole_0 @ X2 @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','20'])).

thf('22',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( X15 != X14 )
      | ( r2_hidden @ X15 @ X16 )
      | ( X16
       != ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('23',plain,(
    ! [X14: $i] :
      ( r2_hidden @ X14 @ ( k1_tarski @ X14 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('29',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    | ( ( k1_tarski @ sk_A )
      = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','33'])).

thf('35',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('38',plain,(
    ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['35','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qBNUphHEYs
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:16:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 3.58/3.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.58/3.78  % Solved by: fo/fo7.sh
% 3.58/3.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.58/3.78  % done 4742 iterations in 3.332s
% 3.58/3.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.58/3.78  % SZS output start Refutation
% 3.58/3.78  thf(sk_A_type, type, sk_A: $i).
% 3.58/3.78  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 3.58/3.78  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.58/3.78  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.58/3.78  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.58/3.78  thf(sk_B_type, type, sk_B: $i).
% 3.58/3.78  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 3.58/3.78  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.58/3.78  thf(d4_xboole_0, axiom,
% 3.58/3.78    (![A:$i,B:$i,C:$i]:
% 3.58/3.78     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 3.58/3.78       ( ![D:$i]:
% 3.58/3.78         ( ( r2_hidden @ D @ C ) <=>
% 3.58/3.78           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 3.58/3.78  thf('0', plain,
% 3.58/3.78      (![X3 : $i, X4 : $i, X7 : $i]:
% 3.58/3.78         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 3.58/3.78          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 3.58/3.78          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 3.58/3.78      inference('cnf', [status(esa)], [d4_xboole_0])).
% 3.58/3.78  thf('1', plain,
% 3.58/3.78      (![X0 : $i, X1 : $i]:
% 3.58/3.78         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 3.58/3.78          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 3.58/3.78      inference('eq_fact', [status(thm)], ['0'])).
% 3.58/3.78  thf(t3_xboole_0, axiom,
% 3.58/3.78    (![A:$i,B:$i]:
% 3.58/3.78     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 3.58/3.78            ( r1_xboole_0 @ A @ B ) ) ) & 
% 3.58/3.78       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 3.58/3.78            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 3.58/3.78  thf('2', plain,
% 3.58/3.78      (![X8 : $i, X9 : $i]:
% 3.58/3.78         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X8))),
% 3.58/3.78      inference('cnf', [status(esa)], [t3_xboole_0])).
% 3.58/3.78  thf(d1_tarski, axiom,
% 3.58/3.78    (![A:$i,B:$i]:
% 3.58/3.78     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 3.58/3.78       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 3.58/3.78  thf('3', plain,
% 3.58/3.78      (![X14 : $i, X16 : $i, X17 : $i]:
% 3.58/3.78         (~ (r2_hidden @ X17 @ X16)
% 3.58/3.78          | ((X17) = (X14))
% 3.58/3.78          | ((X16) != (k1_tarski @ X14)))),
% 3.58/3.78      inference('cnf', [status(esa)], [d1_tarski])).
% 3.58/3.78  thf('4', plain,
% 3.58/3.78      (![X14 : $i, X17 : $i]:
% 3.58/3.78         (((X17) = (X14)) | ~ (r2_hidden @ X17 @ (k1_tarski @ X14)))),
% 3.58/3.78      inference('simplify', [status(thm)], ['3'])).
% 3.58/3.78  thf('5', plain,
% 3.58/3.78      (![X0 : $i, X1 : $i]:
% 3.58/3.78         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 3.58/3.78          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 3.58/3.78      inference('sup-', [status(thm)], ['2', '4'])).
% 3.58/3.78  thf('6', plain,
% 3.58/3.78      (![X8 : $i, X9 : $i]:
% 3.58/3.78         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X9))),
% 3.58/3.78      inference('cnf', [status(esa)], [t3_xboole_0])).
% 3.58/3.78  thf('7', plain,
% 3.58/3.78      (![X0 : $i, X1 : $i]:
% 3.58/3.78         ((r2_hidden @ X0 @ X1)
% 3.58/3.78          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 3.58/3.78          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 3.58/3.78      inference('sup+', [status(thm)], ['5', '6'])).
% 3.58/3.78  thf('8', plain,
% 3.58/3.78      (![X0 : $i, X1 : $i]:
% 3.58/3.78         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 3.58/3.78      inference('simplify', [status(thm)], ['7'])).
% 3.58/3.78  thf('9', plain,
% 3.58/3.78      (![X0 : $i, X1 : $i]:
% 3.58/3.78         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 3.58/3.78      inference('simplify', [status(thm)], ['7'])).
% 3.58/3.78  thf(t58_zfmisc_1, conjecture,
% 3.58/3.78    (![A:$i,B:$i]:
% 3.58/3.78     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 3.58/3.78       ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 3.58/3.78  thf(zf_stmt_0, negated_conjecture,
% 3.58/3.78    (~( ![A:$i,B:$i]:
% 3.58/3.78        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 3.58/3.78          ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )),
% 3.58/3.78    inference('cnf.neg', [status(esa)], [t58_zfmisc_1])).
% 3.58/3.78  thf('10', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)),
% 3.58/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.58/3.78  thf('11', plain, ((r2_hidden @ sk_A @ sk_B)),
% 3.58/3.78      inference('sup-', [status(thm)], ['9', '10'])).
% 3.58/3.78  thf('12', plain,
% 3.58/3.78      (![X8 : $i, X9 : $i]:
% 3.58/3.78         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X9))),
% 3.58/3.78      inference('cnf', [status(esa)], [t3_xboole_0])).
% 3.58/3.78  thf('13', plain,
% 3.58/3.78      (![X14 : $i, X17 : $i]:
% 3.58/3.78         (((X17) = (X14)) | ~ (r2_hidden @ X17 @ (k1_tarski @ X14)))),
% 3.58/3.78      inference('simplify', [status(thm)], ['3'])).
% 3.58/3.78  thf('14', plain,
% 3.58/3.78      (![X0 : $i, X1 : $i]:
% 3.58/3.78         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 3.58/3.78          | ((sk_C @ (k1_tarski @ X0) @ X1) = (X0)))),
% 3.58/3.78      inference('sup-', [status(thm)], ['12', '13'])).
% 3.58/3.78  thf('15', plain,
% 3.58/3.78      (![X8 : $i, X9 : $i]:
% 3.58/3.78         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X8))),
% 3.58/3.78      inference('cnf', [status(esa)], [t3_xboole_0])).
% 3.58/3.78  thf('16', plain,
% 3.58/3.78      (![X8 : $i, X10 : $i, X11 : $i]:
% 3.58/3.78         (~ (r2_hidden @ X10 @ X8)
% 3.58/3.78          | ~ (r2_hidden @ X10 @ X11)
% 3.58/3.78          | ~ (r1_xboole_0 @ X8 @ X11))),
% 3.58/3.78      inference('cnf', [status(esa)], [t3_xboole_0])).
% 3.58/3.78  thf('17', plain,
% 3.58/3.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.58/3.78         ((r1_xboole_0 @ X0 @ X1)
% 3.58/3.78          | ~ (r1_xboole_0 @ X0 @ X2)
% 3.58/3.78          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 3.58/3.78      inference('sup-', [status(thm)], ['15', '16'])).
% 3.58/3.78  thf('18', plain,
% 3.58/3.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.58/3.78         (~ (r2_hidden @ X0 @ X1)
% 3.58/3.78          | (r1_xboole_0 @ X2 @ (k1_tarski @ X0))
% 3.58/3.78          | ~ (r1_xboole_0 @ X2 @ X1)
% 3.58/3.78          | (r1_xboole_0 @ X2 @ (k1_tarski @ X0)))),
% 3.58/3.78      inference('sup-', [status(thm)], ['14', '17'])).
% 3.58/3.78  thf('19', plain,
% 3.58/3.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.58/3.78         (~ (r1_xboole_0 @ X2 @ X1)
% 3.58/3.78          | (r1_xboole_0 @ X2 @ (k1_tarski @ X0))
% 3.58/3.78          | ~ (r2_hidden @ X0 @ X1))),
% 3.58/3.78      inference('simplify', [status(thm)], ['18'])).
% 3.58/3.78  thf('20', plain,
% 3.58/3.78      (![X0 : $i]:
% 3.58/3.78         ((r1_xboole_0 @ X0 @ (k1_tarski @ sk_A)) | ~ (r1_xboole_0 @ X0 @ sk_B))),
% 3.58/3.78      inference('sup-', [status(thm)], ['11', '19'])).
% 3.58/3.78  thf('21', plain,
% 3.58/3.78      (![X0 : $i]:
% 3.58/3.78         ((r2_hidden @ X0 @ sk_B)
% 3.58/3.78          | (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ sk_A)))),
% 3.58/3.78      inference('sup-', [status(thm)], ['8', '20'])).
% 3.58/3.78  thf('22', plain,
% 3.58/3.78      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.58/3.78         (((X15) != (X14))
% 3.58/3.78          | (r2_hidden @ X15 @ X16)
% 3.58/3.78          | ((X16) != (k1_tarski @ X14)))),
% 3.58/3.78      inference('cnf', [status(esa)], [d1_tarski])).
% 3.58/3.78  thf('23', plain, (![X14 : $i]: (r2_hidden @ X14 @ (k1_tarski @ X14))),
% 3.58/3.78      inference('simplify', [status(thm)], ['22'])).
% 3.58/3.78  thf('24', plain,
% 3.58/3.78      (![X8 : $i, X10 : $i, X11 : $i]:
% 3.58/3.78         (~ (r2_hidden @ X10 @ X8)
% 3.58/3.78          | ~ (r2_hidden @ X10 @ X11)
% 3.58/3.78          | ~ (r1_xboole_0 @ X8 @ X11))),
% 3.58/3.78      inference('cnf', [status(esa)], [t3_xboole_0])).
% 3.58/3.78  thf('25', plain,
% 3.58/3.78      (![X0 : $i, X1 : $i]:
% 3.58/3.78         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 3.58/3.78      inference('sup-', [status(thm)], ['23', '24'])).
% 3.58/3.78  thf('26', plain,
% 3.58/3.78      (![X0 : $i]:
% 3.58/3.78         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 3.58/3.78      inference('sup-', [status(thm)], ['21', '25'])).
% 3.58/3.78  thf('27', plain,
% 3.58/3.78      (![X0 : $i]:
% 3.58/3.78         (((k1_tarski @ sk_A) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_A)))
% 3.58/3.78          | (r2_hidden @ 
% 3.58/3.78             (sk_D @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A) @ X0) @ sk_B))),
% 3.58/3.78      inference('sup-', [status(thm)], ['1', '26'])).
% 3.58/3.78  thf('28', plain,
% 3.58/3.78      (![X0 : $i, X1 : $i]:
% 3.58/3.78         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 3.58/3.78          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 3.58/3.78      inference('eq_fact', [status(thm)], ['0'])).
% 3.58/3.78  thf('29', plain,
% 3.58/3.78      (![X3 : $i, X4 : $i, X7 : $i]:
% 3.58/3.78         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 3.58/3.78          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 3.58/3.78          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 3.58/3.78          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 3.58/3.78      inference('cnf', [status(esa)], [d4_xboole_0])).
% 3.58/3.78  thf('30', plain,
% 3.58/3.78      (![X0 : $i, X1 : $i]:
% 3.58/3.78         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 3.58/3.78          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 3.58/3.78          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 3.58/3.78          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 3.58/3.78      inference('sup-', [status(thm)], ['28', '29'])).
% 3.58/3.78  thf('31', plain,
% 3.58/3.78      (![X0 : $i, X1 : $i]:
% 3.58/3.78         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 3.58/3.78          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 3.58/3.78          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 3.58/3.78      inference('simplify', [status(thm)], ['30'])).
% 3.58/3.78  thf('32', plain,
% 3.58/3.78      (![X0 : $i, X1 : $i]:
% 3.58/3.78         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 3.58/3.78          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 3.58/3.78      inference('eq_fact', [status(thm)], ['0'])).
% 3.58/3.78  thf('33', plain,
% 3.58/3.78      (![X0 : $i, X1 : $i]:
% 3.58/3.78         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 3.58/3.78          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 3.58/3.78      inference('clc', [status(thm)], ['31', '32'])).
% 3.58/3.78  thf('34', plain,
% 3.58/3.78      ((((k1_tarski @ sk_A) = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 3.58/3.78        | ((k1_tarski @ sk_A) = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 3.58/3.78      inference('sup-', [status(thm)], ['27', '33'])).
% 3.58/3.78  thf('35', plain,
% 3.58/3.78      (((k1_tarski @ sk_A) = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 3.58/3.78      inference('simplify', [status(thm)], ['34'])).
% 3.58/3.78  thf('36', plain,
% 3.58/3.78      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 3.58/3.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.58/3.78  thf(commutativity_k3_xboole_0, axiom,
% 3.58/3.78    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 3.58/3.78  thf('37', plain,
% 3.58/3.78      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.58/3.78      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.58/3.78  thf('38', plain,
% 3.58/3.78      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (k1_tarski @ sk_A))),
% 3.58/3.78      inference('demod', [status(thm)], ['36', '37'])).
% 3.58/3.78  thf('39', plain, ($false),
% 3.58/3.78      inference('simplify_reflect-', [status(thm)], ['35', '38'])).
% 3.58/3.78  
% 3.58/3.78  % SZS output end Refutation
% 3.58/3.78  
% 3.65/3.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
