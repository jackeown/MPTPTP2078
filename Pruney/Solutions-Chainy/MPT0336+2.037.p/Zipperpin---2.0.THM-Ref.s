%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dYzeiJ7pJk

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:25 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   62 (  81 expanded)
%              Number of leaves         :   19 (  32 expanded)
%              Depth                    :   14
%              Number of atoms          :  420 ( 680 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t149_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ C )
        & ( r1_xboole_0 @ C @ B ) )
     => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ C )
          & ( r1_xboole_0 @ C @ B ) )
       => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t149_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_3 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_C_3 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    r1_xboole_0 @ sk_B @ sk_C_3 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_xboole_0 @ sk_B @ sk_C_3 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('5',plain,(
    r2_hidden @ sk_D @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('7',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ( X21 = X18 )
      | ( X20
       != ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('8',plain,(
    ! [X18: $i,X21: $i] :
      ( ( X21 = X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_tarski @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('11',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ X2 @ ( k1_tarski @ X0 ) )
      | ~ ( r1_xboole_0 @ X2 @ X1 )
      | ( r1_xboole_0 @ X2 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X1 )
      | ( r1_xboole_0 @ X2 @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k1_tarski @ sk_D ) )
      | ~ ( r1_xboole_0 @ X0 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['5','14'])).

thf('16',plain,(
    r1_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) ),
    inference('sup-',[status(thm)],['4','15'])).

thf('17',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('18',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('20',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_D ) )
      | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('25',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ ( k1_tarski @ sk_D ) )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k1_tarski @ sk_D ) )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['16','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t75_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) )).

thf('31',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_xboole_0 @ X16 @ X17 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t75_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('35',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('36',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) )
      | ~ ( r1_xboole_0 @ X12 @ X13 )
      | ~ ( r1_xboole_0 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['3','37'])).

thf('39',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('40',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_3 ) @ sk_B ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['0','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dYzeiJ7pJk
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:18:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.58  % Solved by: fo/fo7.sh
% 0.19/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.58  % done 342 iterations in 0.162s
% 0.19/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.58  % SZS output start Refutation
% 0.19/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.58  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.58  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.19/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.58  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.19/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.58  thf(t149_zfmisc_1, conjecture,
% 0.19/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.58     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.19/0.58         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.19/0.58       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.19/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.58    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.58        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.19/0.58            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.19/0.58          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 0.19/0.58    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 0.19/0.58  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_3) @ sk_B)),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.58  thf('1', plain, ((r1_xboole_0 @ sk_C_3 @ sk_B)),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.58  thf(symmetry_r1_xboole_0, axiom,
% 0.19/0.58    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.19/0.58  thf('2', plain,
% 0.19/0.58      (![X6 : $i, X7 : $i]:
% 0.19/0.58         ((r1_xboole_0 @ X6 @ X7) | ~ (r1_xboole_0 @ X7 @ X6))),
% 0.19/0.58      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.19/0.58  thf('3', plain, ((r1_xboole_0 @ sk_B @ sk_C_3)),
% 0.19/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.58  thf('4', plain, ((r1_xboole_0 @ sk_B @ sk_C_3)),
% 0.19/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.58  thf('5', plain, ((r2_hidden @ sk_D @ sk_C_3)),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.58  thf(t3_xboole_0, axiom,
% 0.19/0.58    (![A:$i,B:$i]:
% 0.19/0.58     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.19/0.58            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.58       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.19/0.58            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.19/0.58  thf('6', plain,
% 0.19/0.58      (![X8 : $i, X9 : $i]:
% 0.19/0.58         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C_1 @ X9 @ X8) @ X9))),
% 0.19/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.58  thf(d1_tarski, axiom,
% 0.19/0.58    (![A:$i,B:$i]:
% 0.19/0.58     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.19/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.19/0.58  thf('7', plain,
% 0.19/0.58      (![X18 : $i, X20 : $i, X21 : $i]:
% 0.19/0.58         (~ (r2_hidden @ X21 @ X20)
% 0.19/0.58          | ((X21) = (X18))
% 0.19/0.58          | ((X20) != (k1_tarski @ X18)))),
% 0.19/0.58      inference('cnf', [status(esa)], [d1_tarski])).
% 0.19/0.58  thf('8', plain,
% 0.19/0.58      (![X18 : $i, X21 : $i]:
% 0.19/0.58         (((X21) = (X18)) | ~ (r2_hidden @ X21 @ (k1_tarski @ X18)))),
% 0.19/0.58      inference('simplify', [status(thm)], ['7'])).
% 0.19/0.58  thf('9', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i]:
% 0.19/0.58         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.19/0.58          | ((sk_C_1 @ (k1_tarski @ X0) @ X1) = (X0)))),
% 0.19/0.58      inference('sup-', [status(thm)], ['6', '8'])).
% 0.19/0.58  thf('10', plain,
% 0.19/0.58      (![X8 : $i, X9 : $i]:
% 0.19/0.58         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C_1 @ X9 @ X8) @ X8))),
% 0.19/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.58  thf('11', plain,
% 0.19/0.58      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.19/0.58         (~ (r2_hidden @ X10 @ X8)
% 0.19/0.58          | ~ (r2_hidden @ X10 @ X11)
% 0.19/0.58          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.19/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.58  thf('12', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.58         ((r1_xboole_0 @ X0 @ X1)
% 0.19/0.58          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.19/0.58          | ~ (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X2))),
% 0.19/0.58      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.58  thf('13', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.58         (~ (r2_hidden @ X0 @ X1)
% 0.19/0.58          | (r1_xboole_0 @ X2 @ (k1_tarski @ X0))
% 0.19/0.58          | ~ (r1_xboole_0 @ X2 @ X1)
% 0.19/0.58          | (r1_xboole_0 @ X2 @ (k1_tarski @ X0)))),
% 0.19/0.58      inference('sup-', [status(thm)], ['9', '12'])).
% 0.19/0.58  thf('14', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.58         (~ (r1_xboole_0 @ X2 @ X1)
% 0.19/0.58          | (r1_xboole_0 @ X2 @ (k1_tarski @ X0))
% 0.19/0.58          | ~ (r2_hidden @ X0 @ X1))),
% 0.19/0.58      inference('simplify', [status(thm)], ['13'])).
% 0.19/0.58  thf('15', plain,
% 0.19/0.58      (![X0 : $i]:
% 0.19/0.58         ((r1_xboole_0 @ X0 @ (k1_tarski @ sk_D))
% 0.19/0.58          | ~ (r1_xboole_0 @ X0 @ sk_C_3))),
% 0.19/0.58      inference('sup-', [status(thm)], ['5', '14'])).
% 0.19/0.58  thf('16', plain, ((r1_xboole_0 @ sk_B @ (k1_tarski @ sk_D))),
% 0.19/0.58      inference('sup-', [status(thm)], ['4', '15'])).
% 0.19/0.58  thf('17', plain,
% 0.19/0.58      (![X8 : $i, X9 : $i]:
% 0.19/0.58         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C_1 @ X9 @ X8) @ X8))),
% 0.19/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.58  thf('18', plain,
% 0.19/0.58      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 0.19/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.58  thf(commutativity_k3_xboole_0, axiom,
% 0.19/0.58    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.19/0.58  thf('19', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.58  thf('20', plain,
% 0.19/0.58      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 0.19/0.58      inference('demod', [status(thm)], ['18', '19'])).
% 0.19/0.58  thf(d3_tarski, axiom,
% 0.19/0.58    (![A:$i,B:$i]:
% 0.19/0.58     ( ( r1_tarski @ A @ B ) <=>
% 0.19/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.19/0.58  thf('21', plain,
% 0.19/0.58      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.58         (~ (r2_hidden @ X2 @ X3)
% 0.19/0.58          | (r2_hidden @ X2 @ X4)
% 0.19/0.58          | ~ (r1_tarski @ X3 @ X4))),
% 0.19/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.58  thf('22', plain,
% 0.19/0.58      (![X0 : $i]:
% 0.19/0.58         ((r2_hidden @ X0 @ (k1_tarski @ sk_D))
% 0.19/0.58          | ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.19/0.58      inference('sup-', [status(thm)], ['20', '21'])).
% 0.19/0.58  thf('23', plain,
% 0.19/0.58      (![X0 : $i]:
% 0.19/0.58         ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ X0)
% 0.19/0.58          | (r2_hidden @ (sk_C_1 @ X0 @ (k3_xboole_0 @ sk_B @ sk_A)) @ 
% 0.19/0.58             (k1_tarski @ sk_D)))),
% 0.19/0.58      inference('sup-', [status(thm)], ['17', '22'])).
% 0.19/0.58  thf('24', plain,
% 0.19/0.58      (![X8 : $i, X9 : $i]:
% 0.19/0.58         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C_1 @ X9 @ X8) @ X9))),
% 0.19/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.58  thf('25', plain,
% 0.19/0.58      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.19/0.58         (~ (r2_hidden @ X10 @ X8)
% 0.19/0.58          | ~ (r2_hidden @ X10 @ X11)
% 0.19/0.58          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.19/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.58  thf('26', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.58         ((r1_xboole_0 @ X1 @ X0)
% 0.19/0.58          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.19/0.58          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X2))),
% 0.19/0.58      inference('sup-', [status(thm)], ['24', '25'])).
% 0.19/0.58  thf('27', plain,
% 0.19/0.58      (![X0 : $i]:
% 0.19/0.58         ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ X0)
% 0.19/0.58          | ~ (r1_xboole_0 @ X0 @ (k1_tarski @ sk_D))
% 0.19/0.58          | (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ X0))),
% 0.19/0.58      inference('sup-', [status(thm)], ['23', '26'])).
% 0.19/0.58  thf('28', plain,
% 0.19/0.58      (![X0 : $i]:
% 0.19/0.58         (~ (r1_xboole_0 @ X0 @ (k1_tarski @ sk_D))
% 0.19/0.58          | (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ X0))),
% 0.19/0.58      inference('simplify', [status(thm)], ['27'])).
% 0.19/0.58  thf('29', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_B)),
% 0.19/0.58      inference('sup-', [status(thm)], ['16', '28'])).
% 0.19/0.58  thf('30', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.58  thf(t75_xboole_1, axiom,
% 0.19/0.58    (![A:$i,B:$i]:
% 0.19/0.58     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.19/0.58          ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) ))).
% 0.19/0.58  thf('31', plain,
% 0.19/0.58      (![X16 : $i, X17 : $i]:
% 0.19/0.58         ((r1_xboole_0 @ X16 @ X17)
% 0.19/0.58          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X17))),
% 0.19/0.58      inference('cnf', [status(esa)], [t75_xboole_1])).
% 0.19/0.58  thf('32', plain,
% 0.19/0.58      (![X0 : $i, X1 : $i]:
% 0.19/0.58         (~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 0.19/0.58          | (r1_xboole_0 @ X0 @ X1))),
% 0.19/0.58      inference('sup-', [status(thm)], ['30', '31'])).
% 0.19/0.58  thf('33', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.19/0.58      inference('sup-', [status(thm)], ['29', '32'])).
% 0.19/0.58  thf('34', plain,
% 0.19/0.58      (![X6 : $i, X7 : $i]:
% 0.19/0.58         ((r1_xboole_0 @ X6 @ X7) | ~ (r1_xboole_0 @ X7 @ X6))),
% 0.19/0.58      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.19/0.58  thf('35', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 0.19/0.58      inference('sup-', [status(thm)], ['33', '34'])).
% 0.19/0.58  thf(t70_xboole_1, axiom,
% 0.19/0.58    (![A:$i,B:$i,C:$i]:
% 0.19/0.58     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.19/0.58            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.19/0.58       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.19/0.58            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.19/0.58  thf('36', plain,
% 0.19/0.58      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.58         ((r1_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14))
% 0.19/0.58          | ~ (r1_xboole_0 @ X12 @ X13)
% 0.19/0.58          | ~ (r1_xboole_0 @ X12 @ X14))),
% 0.19/0.58      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.19/0.58  thf('37', plain,
% 0.19/0.58      (![X0 : $i]:
% 0.19/0.58         (~ (r1_xboole_0 @ sk_B @ X0)
% 0.19/0.58          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 0.19/0.58      inference('sup-', [status(thm)], ['35', '36'])).
% 0.19/0.58  thf('38', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_3))),
% 0.19/0.58      inference('sup-', [status(thm)], ['3', '37'])).
% 0.19/0.58  thf('39', plain,
% 0.19/0.58      (![X6 : $i, X7 : $i]:
% 0.19/0.58         ((r1_xboole_0 @ X6 @ X7) | ~ (r1_xboole_0 @ X7 @ X6))),
% 0.19/0.58      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.19/0.58  thf('40', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_3) @ sk_B)),
% 0.19/0.58      inference('sup-', [status(thm)], ['38', '39'])).
% 0.19/0.58  thf('41', plain, ($false), inference('demod', [status(thm)], ['0', '40'])).
% 0.19/0.58  
% 0.19/0.58  % SZS output end Refutation
% 0.19/0.58  
% 0.19/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
