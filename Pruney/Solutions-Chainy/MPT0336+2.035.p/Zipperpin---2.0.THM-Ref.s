%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7zqhsK38P0

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:24 EST 2020

% Result     : Theorem 0.81s
% Output     : Refutation 0.81s
% Verified   : 
% Statistics : Number of formulae       :   66 (  80 expanded)
%              Number of leaves         :   23 (  33 expanded)
%              Depth                    :   13
%              Number of atoms          :  430 ( 651 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_4_type,type,(
    sk_C_4: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_4 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_C_4 @ sk_B ),
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
    r1_xboole_0 @ sk_B @ sk_C_4 ),
    inference('sup-',[status(thm)],['1','2'])).

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

thf('4',plain,(
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

thf('5',plain,(
    ! [X24: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X27 @ X26 )
      | ( X27 = X24 )
      | ( X26
       != ( k1_tarski @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('6',plain,(
    ! [X24: $i,X27: $i] :
      ( ( X27 = X24 )
      | ~ ( r2_hidden @ X27 @ ( k1_tarski @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C_2 @ X13 @ X12 ) @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('12',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('14',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_D ) )
      | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C_2 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C_2 @ X13 @ X12 ) @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('20',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_A )
    | ~ ( r1_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) )
    | ( r1_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['17','26'])).

thf('28',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) )
    | ( r1_xboole_0 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( r2_hidden @ sk_D @ sk_B )
    | ( r1_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['10','28'])).

thf('30',plain,(
    r1_xboole_0 @ sk_C_4 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    r2_hidden @ sk_D @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_4 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( r2_hidden @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['29','34'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('36',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r1_xboole_0 @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) )
      | ~ ( r1_xboole_0 @ X20 @ X21 )
      | ~ ( r1_xboole_0 @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['3','37'])).

thf('39',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('40',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_4 ) @ sk_B ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['0','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7zqhsK38P0
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:47:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.81/1.04  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.81/1.04  % Solved by: fo/fo7.sh
% 0.81/1.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.81/1.04  % done 1243 iterations in 0.546s
% 0.81/1.04  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.81/1.04  % SZS output start Refutation
% 0.81/1.04  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.81/1.04  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.81/1.04  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.81/1.04  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.81/1.04  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.81/1.04  thf(sk_B_type, type, sk_B: $i).
% 0.81/1.04  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.81/1.04  thf(sk_A_type, type, sk_A: $i).
% 0.81/1.04  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.81/1.04  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.81/1.04  thf(sk_C_4_type, type, sk_C_4: $i).
% 0.81/1.04  thf(sk_D_type, type, sk_D: $i).
% 0.81/1.04  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.81/1.04  thf(t149_zfmisc_1, conjecture,
% 0.81/1.04    (![A:$i,B:$i,C:$i,D:$i]:
% 0.81/1.04     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.81/1.04         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.81/1.04       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.81/1.04  thf(zf_stmt_0, negated_conjecture,
% 0.81/1.04    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.81/1.04        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.81/1.04            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.81/1.04          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 0.81/1.04    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 0.81/1.04  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_4) @ sk_B)),
% 0.81/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.04  thf('1', plain, ((r1_xboole_0 @ sk_C_4 @ sk_B)),
% 0.81/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.04  thf(symmetry_r1_xboole_0, axiom,
% 0.81/1.04    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.81/1.04  thf('2', plain,
% 0.81/1.04      (![X6 : $i, X7 : $i]:
% 0.81/1.04         ((r1_xboole_0 @ X6 @ X7) | ~ (r1_xboole_0 @ X7 @ X6))),
% 0.81/1.04      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.81/1.04  thf('3', plain, ((r1_xboole_0 @ sk_B @ sk_C_4)),
% 0.81/1.04      inference('sup-', [status(thm)], ['1', '2'])).
% 0.81/1.04  thf(t3_xboole_0, axiom,
% 0.81/1.04    (![A:$i,B:$i]:
% 0.81/1.04     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.81/1.04            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.81/1.04       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.81/1.04            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.81/1.04  thf('4', plain,
% 0.81/1.04      (![X8 : $i, X9 : $i]:
% 0.81/1.04         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C_1 @ X9 @ X8) @ X9))),
% 0.81/1.04      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.81/1.04  thf(d1_tarski, axiom,
% 0.81/1.04    (![A:$i,B:$i]:
% 0.81/1.04     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.81/1.04       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.81/1.04  thf('5', plain,
% 0.81/1.04      (![X24 : $i, X26 : $i, X27 : $i]:
% 0.81/1.04         (~ (r2_hidden @ X27 @ X26)
% 0.81/1.04          | ((X27) = (X24))
% 0.81/1.04          | ((X26) != (k1_tarski @ X24)))),
% 0.81/1.04      inference('cnf', [status(esa)], [d1_tarski])).
% 0.81/1.04  thf('6', plain,
% 0.81/1.04      (![X24 : $i, X27 : $i]:
% 0.81/1.04         (((X27) = (X24)) | ~ (r2_hidden @ X27 @ (k1_tarski @ X24)))),
% 0.81/1.04      inference('simplify', [status(thm)], ['5'])).
% 0.81/1.04  thf('7', plain,
% 0.81/1.04      (![X0 : $i, X1 : $i]:
% 0.81/1.04         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.81/1.04          | ((sk_C_1 @ (k1_tarski @ X0) @ X1) = (X0)))),
% 0.81/1.04      inference('sup-', [status(thm)], ['4', '6'])).
% 0.81/1.04  thf('8', plain,
% 0.81/1.04      (![X8 : $i, X9 : $i]:
% 0.81/1.04         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C_1 @ X9 @ X8) @ X8))),
% 0.81/1.04      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.81/1.04  thf('9', plain,
% 0.81/1.04      (![X0 : $i, X1 : $i]:
% 0.81/1.04         ((r2_hidden @ X0 @ X1)
% 0.81/1.04          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.81/1.04          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.81/1.04      inference('sup+', [status(thm)], ['7', '8'])).
% 0.81/1.04  thf('10', plain,
% 0.81/1.04      (![X0 : $i, X1 : $i]:
% 0.81/1.04         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0)) | (r2_hidden @ X0 @ X1))),
% 0.81/1.04      inference('simplify', [status(thm)], ['9'])).
% 0.81/1.04  thf(t4_xboole_0, axiom,
% 0.81/1.04    (![A:$i,B:$i]:
% 0.81/1.04     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.81/1.04            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.81/1.04       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.81/1.04            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.81/1.04  thf('11', plain,
% 0.81/1.04      (![X12 : $i, X13 : $i]:
% 0.81/1.04         ((r1_xboole_0 @ X12 @ X13)
% 0.81/1.04          | (r2_hidden @ (sk_C_2 @ X13 @ X12) @ (k3_xboole_0 @ X12 @ X13)))),
% 0.81/1.04      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.81/1.04  thf('12', plain,
% 0.81/1.04      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 0.81/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.04  thf(commutativity_k3_xboole_0, axiom,
% 0.81/1.04    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.81/1.04  thf('13', plain,
% 0.81/1.04      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.81/1.04      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.81/1.04  thf('14', plain,
% 0.81/1.04      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 0.81/1.04      inference('demod', [status(thm)], ['12', '13'])).
% 0.81/1.04  thf(d3_tarski, axiom,
% 0.81/1.04    (![A:$i,B:$i]:
% 0.81/1.04     ( ( r1_tarski @ A @ B ) <=>
% 0.81/1.04       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.81/1.04  thf('15', plain,
% 0.81/1.04      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.81/1.04         (~ (r2_hidden @ X2 @ X3)
% 0.81/1.04          | (r2_hidden @ X2 @ X4)
% 0.81/1.04          | ~ (r1_tarski @ X3 @ X4))),
% 0.81/1.04      inference('cnf', [status(esa)], [d3_tarski])).
% 0.81/1.04  thf('16', plain,
% 0.81/1.04      (![X0 : $i]:
% 0.81/1.04         ((r2_hidden @ X0 @ (k1_tarski @ sk_D))
% 0.81/1.04          | ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.81/1.04      inference('sup-', [status(thm)], ['14', '15'])).
% 0.81/1.04  thf('17', plain,
% 0.81/1.04      (((r1_xboole_0 @ sk_B @ sk_A)
% 0.81/1.04        | (r2_hidden @ (sk_C_2 @ sk_A @ sk_B) @ (k1_tarski @ sk_D)))),
% 0.81/1.04      inference('sup-', [status(thm)], ['11', '16'])).
% 0.81/1.04  thf('18', plain,
% 0.81/1.04      (![X12 : $i, X13 : $i]:
% 0.81/1.04         ((r1_xboole_0 @ X12 @ X13)
% 0.81/1.04          | (r2_hidden @ (sk_C_2 @ X13 @ X12) @ (k3_xboole_0 @ X12 @ X13)))),
% 0.81/1.04      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.81/1.04  thf(t48_xboole_1, axiom,
% 0.81/1.04    (![A:$i,B:$i]:
% 0.81/1.04     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.81/1.04  thf('19', plain,
% 0.81/1.04      (![X18 : $i, X19 : $i]:
% 0.81/1.04         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.81/1.04           = (k3_xboole_0 @ X18 @ X19))),
% 0.81/1.04      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.81/1.04  thf(t36_xboole_1, axiom,
% 0.81/1.04    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.81/1.04  thf('20', plain,
% 0.81/1.04      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 0.81/1.04      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.81/1.04  thf('21', plain,
% 0.81/1.04      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.81/1.04      inference('sup+', [status(thm)], ['19', '20'])).
% 0.81/1.04  thf('22', plain,
% 0.81/1.04      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.81/1.04         (~ (r2_hidden @ X2 @ X3)
% 0.81/1.04          | (r2_hidden @ X2 @ X4)
% 0.81/1.04          | ~ (r1_tarski @ X3 @ X4))),
% 0.81/1.04      inference('cnf', [status(esa)], [d3_tarski])).
% 0.81/1.04  thf('23', plain,
% 0.81/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.04         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.81/1.04      inference('sup-', [status(thm)], ['21', '22'])).
% 0.81/1.04  thf('24', plain,
% 0.81/1.04      (![X0 : $i, X1 : $i]:
% 0.81/1.04         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C_2 @ X0 @ X1) @ X1))),
% 0.81/1.04      inference('sup-', [status(thm)], ['18', '23'])).
% 0.81/1.04  thf('25', plain,
% 0.81/1.04      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.81/1.04         (~ (r2_hidden @ X10 @ X8)
% 0.81/1.04          | ~ (r2_hidden @ X10 @ X11)
% 0.81/1.04          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.81/1.04      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.81/1.04  thf('26', plain,
% 0.81/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.04         ((r1_xboole_0 @ X0 @ X1)
% 0.81/1.04          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.81/1.04          | ~ (r2_hidden @ (sk_C_2 @ X1 @ X0) @ X2))),
% 0.81/1.04      inference('sup-', [status(thm)], ['24', '25'])).
% 0.81/1.04  thf('27', plain,
% 0.81/1.04      (((r1_xboole_0 @ sk_B @ sk_A)
% 0.81/1.04        | ~ (r1_xboole_0 @ sk_B @ (k1_tarski @ sk_D))
% 0.81/1.04        | (r1_xboole_0 @ sk_B @ sk_A))),
% 0.81/1.04      inference('sup-', [status(thm)], ['17', '26'])).
% 0.81/1.04  thf('28', plain,
% 0.81/1.04      ((~ (r1_xboole_0 @ sk_B @ (k1_tarski @ sk_D))
% 0.81/1.04        | (r1_xboole_0 @ sk_B @ sk_A))),
% 0.81/1.04      inference('simplify', [status(thm)], ['27'])).
% 0.81/1.04  thf('29', plain, (((r2_hidden @ sk_D @ sk_B) | (r1_xboole_0 @ sk_B @ sk_A))),
% 0.81/1.04      inference('sup-', [status(thm)], ['10', '28'])).
% 0.81/1.04  thf('30', plain, ((r1_xboole_0 @ sk_C_4 @ sk_B)),
% 0.81/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.04  thf('31', plain, ((r2_hidden @ sk_D @ sk_C_4)),
% 0.81/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.04  thf('32', plain,
% 0.81/1.04      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.81/1.04         (~ (r2_hidden @ X10 @ X8)
% 0.81/1.04          | ~ (r2_hidden @ X10 @ X11)
% 0.81/1.04          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.81/1.04      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.81/1.04  thf('33', plain,
% 0.81/1.04      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_4 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 0.81/1.04      inference('sup-', [status(thm)], ['31', '32'])).
% 0.81/1.04  thf('34', plain, (~ (r2_hidden @ sk_D @ sk_B)),
% 0.81/1.04      inference('sup-', [status(thm)], ['30', '33'])).
% 0.81/1.04  thf('35', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 0.81/1.04      inference('clc', [status(thm)], ['29', '34'])).
% 0.81/1.04  thf(t70_xboole_1, axiom,
% 0.81/1.04    (![A:$i,B:$i,C:$i]:
% 0.81/1.04     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.81/1.04            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.81/1.04       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.81/1.04            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.81/1.04  thf('36', plain,
% 0.81/1.04      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.81/1.04         ((r1_xboole_0 @ X20 @ (k2_xboole_0 @ X21 @ X22))
% 0.81/1.04          | ~ (r1_xboole_0 @ X20 @ X21)
% 0.81/1.04          | ~ (r1_xboole_0 @ X20 @ X22))),
% 0.81/1.04      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.81/1.04  thf('37', plain,
% 0.81/1.04      (![X0 : $i]:
% 0.81/1.04         (~ (r1_xboole_0 @ sk_B @ X0)
% 0.81/1.04          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 0.81/1.04      inference('sup-', [status(thm)], ['35', '36'])).
% 0.81/1.04  thf('38', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_4))),
% 0.81/1.04      inference('sup-', [status(thm)], ['3', '37'])).
% 0.81/1.04  thf('39', plain,
% 0.81/1.04      (![X6 : $i, X7 : $i]:
% 0.81/1.04         ((r1_xboole_0 @ X6 @ X7) | ~ (r1_xboole_0 @ X7 @ X6))),
% 0.81/1.04      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.81/1.04  thf('40', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_4) @ sk_B)),
% 0.81/1.04      inference('sup-', [status(thm)], ['38', '39'])).
% 0.81/1.04  thf('41', plain, ($false), inference('demod', [status(thm)], ['0', '40'])).
% 0.81/1.04  
% 0.81/1.04  % SZS output end Refutation
% 0.81/1.04  
% 0.81/1.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
