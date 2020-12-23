%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.In8jynFjHs

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:23 EST 2020

% Result     : Theorem 1.18s
% Output     : Refutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 137 expanded)
%              Number of leaves         :   22 (  50 expanded)
%              Depth                    :   18
%              Number of atoms          :  470 (1165 expanded)
%              Number of equality atoms :   20 (  34 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('4',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X31 ) @ X32 )
      | ( r2_hidden @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ( r1_xboole_0 @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) )
      | ~ ( r1_xboole_0 @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ( r1_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    r2_hidden @ sk_D @ sk_C_1 ),
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

thf('13',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ~ ( r2_hidden @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B ),
    inference('sup-',[status(thm)],['6','15'])).

thf('17',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('19',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('20',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_xboole_0 @ X16 @ X17 )
      | ( r1_xboole_0 @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('24',plain,(
    r1_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('25',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k4_xboole_0 @ X22 @ X23 )
        = X22 )
      | ~ ( r1_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('26',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('27',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('28',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('32',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('33',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('36',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ sk_A ) @ sk_B )
    | ( ( k4_xboole_0 @ sk_B @ sk_A )
      = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','37'])).

thf('39',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('40',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['26','29'])).

thf('41',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ! [X22: $i,X24: $i] :
      ( ( r1_xboole_0 @ X22 @ X24 )
      | ( ( k4_xboole_0 @ X22 @ X24 )
       != X22 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('43',plain,
    ( ( sk_B != sk_B )
    | ( r1_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) )
      | ~ ( r1_xboole_0 @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','46'])).

thf('48',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('49',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['0','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.In8jynFjHs
% 0.15/0.38  % Computer   : n013.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 15:48:55 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 1.18/1.38  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.18/1.38  % Solved by: fo/fo7.sh
% 1.18/1.38  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.18/1.38  % done 1786 iterations in 0.895s
% 1.18/1.38  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.18/1.38  % SZS output start Refutation
% 1.18/1.38  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.18/1.38  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.18/1.38  thf(sk_B_type, type, sk_B: $i).
% 1.18/1.38  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.18/1.38  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.18/1.38  thf(sk_A_type, type, sk_A: $i).
% 1.18/1.38  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.18/1.38  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.18/1.38  thf(sk_D_type, type, sk_D: $i).
% 1.18/1.38  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.18/1.38  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.18/1.38  thf(t149_zfmisc_1, conjecture,
% 1.18/1.38    (![A:$i,B:$i,C:$i,D:$i]:
% 1.18/1.38     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.18/1.38         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.18/1.38       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.18/1.38  thf(zf_stmt_0, negated_conjecture,
% 1.18/1.38    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.18/1.38        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.18/1.38            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.18/1.38          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 1.18/1.38    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 1.18/1.38  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 1.18/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.38  thf('1', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 1.18/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.38  thf(symmetry_r1_xboole_0, axiom,
% 1.18/1.38    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.18/1.38  thf('2', plain,
% 1.18/1.38      (![X2 : $i, X3 : $i]:
% 1.18/1.38         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 1.18/1.38      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.18/1.38  thf('3', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 1.18/1.38      inference('sup-', [status(thm)], ['1', '2'])).
% 1.18/1.38  thf(l27_zfmisc_1, axiom,
% 1.18/1.38    (![A:$i,B:$i]:
% 1.18/1.38     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 1.18/1.38  thf('4', plain,
% 1.18/1.38      (![X31 : $i, X32 : $i]:
% 1.18/1.38         ((r1_xboole_0 @ (k1_tarski @ X31) @ X32) | (r2_hidden @ X31 @ X32))),
% 1.18/1.38      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 1.18/1.38  thf(t70_xboole_1, axiom,
% 1.18/1.38    (![A:$i,B:$i,C:$i]:
% 1.18/1.38     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 1.18/1.38            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 1.18/1.38       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 1.18/1.38            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 1.18/1.38  thf('5', plain,
% 1.18/1.38      (![X18 : $i, X19 : $i, X21 : $i]:
% 1.18/1.38         ((r1_xboole_0 @ X18 @ X19)
% 1.18/1.38          | ~ (r1_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X21)))),
% 1.18/1.38      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.18/1.38  thf('6', plain,
% 1.18/1.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.18/1.38         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 1.18/1.38          | (r1_xboole_0 @ (k1_tarski @ X2) @ X1))),
% 1.18/1.38      inference('sup-', [status(thm)], ['4', '5'])).
% 1.18/1.38  thf('7', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 1.18/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.39  thf('8', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 1.18/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.39  thf('9', plain,
% 1.18/1.39      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.18/1.39         ((r1_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20))
% 1.18/1.39          | ~ (r1_xboole_0 @ X18 @ X19)
% 1.18/1.39          | ~ (r1_xboole_0 @ X18 @ X20))),
% 1.18/1.39      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.18/1.39  thf('10', plain,
% 1.18/1.39      (![X0 : $i]:
% 1.18/1.39         (~ (r1_xboole_0 @ sk_C_1 @ X0)
% 1.18/1.39          | (r1_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_B @ X0)))),
% 1.18/1.39      inference('sup-', [status(thm)], ['8', '9'])).
% 1.18/1.39  thf('11', plain, ((r1_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_B @ sk_B))),
% 1.18/1.39      inference('sup-', [status(thm)], ['7', '10'])).
% 1.18/1.39  thf('12', plain, ((r2_hidden @ sk_D @ sk_C_1)),
% 1.18/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.39  thf(t3_xboole_0, axiom,
% 1.18/1.39    (![A:$i,B:$i]:
% 1.18/1.39     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.18/1.39            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.18/1.39       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.18/1.39            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.18/1.39  thf('13', plain,
% 1.18/1.39      (![X4 : $i, X6 : $i, X7 : $i]:
% 1.18/1.39         (~ (r2_hidden @ X6 @ X4)
% 1.18/1.39          | ~ (r2_hidden @ X6 @ X7)
% 1.18/1.39          | ~ (r1_xboole_0 @ X4 @ X7))),
% 1.18/1.39      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.18/1.39  thf('14', plain,
% 1.18/1.39      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 1.18/1.39      inference('sup-', [status(thm)], ['12', '13'])).
% 1.18/1.39  thf('15', plain, (~ (r2_hidden @ sk_D @ (k2_xboole_0 @ sk_B @ sk_B))),
% 1.18/1.39      inference('sup-', [status(thm)], ['11', '14'])).
% 1.18/1.39  thf('16', plain, ((r1_xboole_0 @ (k1_tarski @ sk_D) @ sk_B)),
% 1.18/1.39      inference('sup-', [status(thm)], ['6', '15'])).
% 1.18/1.39  thf('17', plain,
% 1.18/1.39      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 1.18/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.39  thf(commutativity_k3_xboole_0, axiom,
% 1.18/1.39    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.18/1.39  thf('18', plain,
% 1.18/1.39      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.18/1.39      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.18/1.39  thf('19', plain,
% 1.18/1.39      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 1.18/1.39      inference('demod', [status(thm)], ['17', '18'])).
% 1.18/1.39  thf(t63_xboole_1, axiom,
% 1.18/1.39    (![A:$i,B:$i,C:$i]:
% 1.18/1.39     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 1.18/1.39       ( r1_xboole_0 @ A @ C ) ))).
% 1.18/1.39  thf('20', plain,
% 1.18/1.39      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.18/1.39         (~ (r1_tarski @ X15 @ X16)
% 1.18/1.39          | ~ (r1_xboole_0 @ X16 @ X17)
% 1.18/1.39          | (r1_xboole_0 @ X15 @ X17))),
% 1.18/1.39      inference('cnf', [status(esa)], [t63_xboole_1])).
% 1.18/1.39  thf('21', plain,
% 1.18/1.39      (![X0 : $i]:
% 1.18/1.39         ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ X0)
% 1.18/1.39          | ~ (r1_xboole_0 @ (k1_tarski @ sk_D) @ X0))),
% 1.18/1.39      inference('sup-', [status(thm)], ['19', '20'])).
% 1.18/1.39  thf('22', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_B)),
% 1.18/1.39      inference('sup-', [status(thm)], ['16', '21'])).
% 1.18/1.39  thf('23', plain,
% 1.18/1.39      (![X2 : $i, X3 : $i]:
% 1.18/1.39         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 1.18/1.39      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.18/1.39  thf('24', plain, ((r1_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_A))),
% 1.18/1.39      inference('sup-', [status(thm)], ['22', '23'])).
% 1.18/1.39  thf(t83_xboole_1, axiom,
% 1.18/1.39    (![A:$i,B:$i]:
% 1.18/1.39     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.18/1.39  thf('25', plain,
% 1.18/1.39      (![X22 : $i, X23 : $i]:
% 1.18/1.39         (((k4_xboole_0 @ X22 @ X23) = (X22)) | ~ (r1_xboole_0 @ X22 @ X23))),
% 1.18/1.39      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.18/1.39  thf('26', plain,
% 1.18/1.39      (((k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_A)) = (sk_B))),
% 1.18/1.39      inference('sup-', [status(thm)], ['24', '25'])).
% 1.18/1.39  thf(t48_xboole_1, axiom,
% 1.18/1.39    (![A:$i,B:$i]:
% 1.18/1.39     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.18/1.39  thf('27', plain,
% 1.18/1.39      (![X13 : $i, X14 : $i]:
% 1.18/1.39         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.18/1.39           = (k3_xboole_0 @ X13 @ X14))),
% 1.18/1.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.18/1.39  thf('28', plain,
% 1.18/1.39      (![X13 : $i, X14 : $i]:
% 1.18/1.39         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.18/1.39           = (k3_xboole_0 @ X13 @ X14))),
% 1.18/1.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.18/1.39  thf('29', plain,
% 1.18/1.39      (![X0 : $i, X1 : $i]:
% 1.18/1.39         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.18/1.39           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.18/1.39      inference('sup+', [status(thm)], ['27', '28'])).
% 1.18/1.39  thf('30', plain,
% 1.18/1.39      (((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_A)) = (sk_B))),
% 1.18/1.39      inference('demod', [status(thm)], ['26', '29'])).
% 1.18/1.39  thf('31', plain,
% 1.18/1.39      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.18/1.39      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.18/1.39  thf('32', plain,
% 1.18/1.39      (![X13 : $i, X14 : $i]:
% 1.18/1.39         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.18/1.39           = (k3_xboole_0 @ X13 @ X14))),
% 1.18/1.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.18/1.39  thf(t36_xboole_1, axiom,
% 1.18/1.39    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.18/1.39  thf('33', plain,
% 1.18/1.39      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 1.18/1.39      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.18/1.39  thf('34', plain,
% 1.18/1.39      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 1.18/1.39      inference('sup+', [status(thm)], ['32', '33'])).
% 1.18/1.39  thf('35', plain,
% 1.18/1.39      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.18/1.39      inference('sup+', [status(thm)], ['31', '34'])).
% 1.18/1.39  thf(d10_xboole_0, axiom,
% 1.18/1.39    (![A:$i,B:$i]:
% 1.18/1.39     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.18/1.39  thf('36', plain,
% 1.18/1.39      (![X8 : $i, X10 : $i]:
% 1.18/1.39         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 1.18/1.39      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.18/1.39  thf('37', plain,
% 1.18/1.39      (![X0 : $i, X1 : $i]:
% 1.18/1.39         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.18/1.39          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.18/1.39      inference('sup-', [status(thm)], ['35', '36'])).
% 1.18/1.39  thf('38', plain,
% 1.18/1.39      ((~ (r1_tarski @ (k4_xboole_0 @ sk_B @ sk_A) @ sk_B)
% 1.18/1.39        | ((k4_xboole_0 @ sk_B @ sk_A)
% 1.18/1.39            = (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_A))))),
% 1.18/1.39      inference('sup-', [status(thm)], ['30', '37'])).
% 1.18/1.39  thf('39', plain,
% 1.18/1.39      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 1.18/1.39      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.18/1.39  thf('40', plain,
% 1.18/1.39      (((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_A)) = (sk_B))),
% 1.18/1.39      inference('demod', [status(thm)], ['26', '29'])).
% 1.18/1.39  thf('41', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 1.18/1.39      inference('demod', [status(thm)], ['38', '39', '40'])).
% 1.18/1.39  thf('42', plain,
% 1.18/1.39      (![X22 : $i, X24 : $i]:
% 1.18/1.39         ((r1_xboole_0 @ X22 @ X24) | ((k4_xboole_0 @ X22 @ X24) != (X22)))),
% 1.18/1.39      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.18/1.39  thf('43', plain, ((((sk_B) != (sk_B)) | (r1_xboole_0 @ sk_B @ sk_A))),
% 1.18/1.39      inference('sup-', [status(thm)], ['41', '42'])).
% 1.18/1.39  thf('44', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 1.18/1.39      inference('simplify', [status(thm)], ['43'])).
% 1.18/1.39  thf('45', plain,
% 1.18/1.39      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.18/1.39         ((r1_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20))
% 1.18/1.39          | ~ (r1_xboole_0 @ X18 @ X19)
% 1.18/1.39          | ~ (r1_xboole_0 @ X18 @ X20))),
% 1.18/1.39      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.18/1.39  thf('46', plain,
% 1.18/1.39      (![X0 : $i]:
% 1.18/1.39         (~ (r1_xboole_0 @ sk_B @ X0)
% 1.18/1.39          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 1.18/1.39      inference('sup-', [status(thm)], ['44', '45'])).
% 1.18/1.39  thf('47', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_1))),
% 1.18/1.39      inference('sup-', [status(thm)], ['3', '46'])).
% 1.18/1.39  thf('48', plain,
% 1.18/1.39      (![X2 : $i, X3 : $i]:
% 1.18/1.39         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 1.18/1.39      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.18/1.39  thf('49', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 1.18/1.39      inference('sup-', [status(thm)], ['47', '48'])).
% 1.18/1.39  thf('50', plain, ($false), inference('demod', [status(thm)], ['0', '49'])).
% 1.18/1.39  
% 1.18/1.39  % SZS output end Refutation
% 1.18/1.39  
% 1.18/1.39  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
