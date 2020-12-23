%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0jMnT9aUpc

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:35 EST 2020

% Result     : Theorem 0.84s
% Output     : Refutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :   70 (  96 expanded)
%              Number of leaves         :   24 (  37 expanded)
%              Depth                    :   12
%              Number of atoms          :  410 ( 639 expanded)
%              Number of equality atoms :   27 (  31 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t106_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
       => ( ( r1_tarski @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t106_xboole_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B_1 )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B_1 )
   <= ~ ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('2',plain,(
    ! [X29: $i,X30: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X29 @ X30 ) @ X30 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('3',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('4',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ X23 @ X24 )
      | ~ ( r1_xboole_0 @ X24 @ X25 )
      | ( r1_xboole_0 @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r1_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C_1 )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('8',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B_1 )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','10'])).

thf('12',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('14',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    = sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','5'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('17',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t74_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r1_xboole_0 @ X26 @ X27 )
      | ( r1_xboole_0 @ X26 @ ( k3_xboole_0 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t74_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('20',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('21',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_C_1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('28',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('29',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C_1 ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('32',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['14','30','31'])).

thf('33',plain,(
    ! [X29: $i,X30: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X29 @ X30 ) @ X30 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('39',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( ( k4_xboole_0 @ X9 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference('sup+',[status(thm)],['32','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['11','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0jMnT9aUpc
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:14:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.84/1.06  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.84/1.06  % Solved by: fo/fo7.sh
% 0.84/1.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.84/1.06  % done 1503 iterations in 0.596s
% 0.84/1.06  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.84/1.06  % SZS output start Refutation
% 0.84/1.06  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.84/1.06  thf(sk_B_type, type, sk_B: $i > $i).
% 0.84/1.06  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.84/1.06  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.84/1.06  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.84/1.06  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.84/1.06  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.84/1.06  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.84/1.06  thf(sk_A_type, type, sk_A: $i).
% 0.84/1.06  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.84/1.06  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.84/1.06  thf(t106_xboole_1, conjecture,
% 0.84/1.06    (![A:$i,B:$i,C:$i]:
% 0.84/1.06     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.84/1.06       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.84/1.06  thf(zf_stmt_0, negated_conjecture,
% 0.84/1.06    (~( ![A:$i,B:$i,C:$i]:
% 0.84/1.06        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.84/1.06          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 0.84/1.06    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 0.84/1.06  thf('0', plain,
% 0.84/1.06      ((~ (r1_tarski @ sk_A @ sk_B_1) | ~ (r1_xboole_0 @ sk_A @ sk_C_1))),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('1', plain,
% 0.84/1.06      ((~ (r1_tarski @ sk_A @ sk_B_1)) <= (~ ((r1_tarski @ sk_A @ sk_B_1)))),
% 0.84/1.06      inference('split', [status(esa)], ['0'])).
% 0.84/1.06  thf(t79_xboole_1, axiom,
% 0.84/1.06    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.84/1.06  thf('2', plain,
% 0.84/1.06      (![X29 : $i, X30 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X29 @ X30) @ X30)),
% 0.84/1.06      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.84/1.06  thf('3', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf(t63_xboole_1, axiom,
% 0.84/1.06    (![A:$i,B:$i,C:$i]:
% 0.84/1.06     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.84/1.06       ( r1_xboole_0 @ A @ C ) ))).
% 0.84/1.06  thf('4', plain,
% 0.84/1.06      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.84/1.06         (~ (r1_tarski @ X23 @ X24)
% 0.84/1.06          | ~ (r1_xboole_0 @ X24 @ X25)
% 0.84/1.06          | (r1_xboole_0 @ X23 @ X25))),
% 0.84/1.06      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.84/1.06  thf('5', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         ((r1_xboole_0 @ sk_A @ X0)
% 0.84/1.06          | ~ (r1_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ sk_C_1) @ X0))),
% 0.84/1.06      inference('sup-', [status(thm)], ['3', '4'])).
% 0.84/1.06  thf('6', plain, ((r1_xboole_0 @ sk_A @ sk_C_1)),
% 0.84/1.06      inference('sup-', [status(thm)], ['2', '5'])).
% 0.84/1.06  thf('7', plain,
% 0.84/1.06      ((~ (r1_xboole_0 @ sk_A @ sk_C_1)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 0.84/1.06      inference('split', [status(esa)], ['0'])).
% 0.84/1.06  thf('8', plain, (((r1_xboole_0 @ sk_A @ sk_C_1))),
% 0.84/1.06      inference('sup-', [status(thm)], ['6', '7'])).
% 0.84/1.06  thf('9', plain,
% 0.84/1.06      (~ ((r1_tarski @ sk_A @ sk_B_1)) | ~ ((r1_xboole_0 @ sk_A @ sk_C_1))),
% 0.84/1.06      inference('split', [status(esa)], ['0'])).
% 0.84/1.06  thf('10', plain, (~ ((r1_tarski @ sk_A @ sk_B_1))),
% 0.84/1.06      inference('sat_resolution*', [status(thm)], ['8', '9'])).
% 0.84/1.06  thf('11', plain, (~ (r1_tarski @ sk_A @ sk_B_1)),
% 0.84/1.06      inference('simpl_trail', [status(thm)], ['1', '10'])).
% 0.84/1.06  thf('12', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf(t28_xboole_1, axiom,
% 0.84/1.06    (![A:$i,B:$i]:
% 0.84/1.06     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.84/1.06  thf('13', plain,
% 0.84/1.06      (![X17 : $i, X18 : $i]:
% 0.84/1.06         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 0.84/1.06      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.84/1.06  thf('14', plain,
% 0.84/1.06      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_C_1)) = (sk_A))),
% 0.84/1.06      inference('sup-', [status(thm)], ['12', '13'])).
% 0.84/1.06  thf('15', plain, ((r1_xboole_0 @ sk_A @ sk_C_1)),
% 0.84/1.06      inference('sup-', [status(thm)], ['2', '5'])).
% 0.84/1.06  thf(symmetry_r1_xboole_0, axiom,
% 0.84/1.06    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.84/1.06  thf('16', plain,
% 0.84/1.06      (![X2 : $i, X3 : $i]:
% 0.84/1.06         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.84/1.06      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.84/1.06  thf('17', plain, ((r1_xboole_0 @ sk_C_1 @ sk_A)),
% 0.84/1.06      inference('sup-', [status(thm)], ['15', '16'])).
% 0.84/1.06  thf(t74_xboole_1, axiom,
% 0.84/1.06    (![A:$i,B:$i,C:$i]:
% 0.84/1.06     ( ~( ( ~( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) & 
% 0.84/1.06          ( r1_xboole_0 @ A @ B ) ) ))).
% 0.84/1.06  thf('18', plain,
% 0.84/1.06      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.84/1.06         (~ (r1_xboole_0 @ X26 @ X27)
% 0.84/1.06          | (r1_xboole_0 @ X26 @ (k3_xboole_0 @ X27 @ X28)))),
% 0.84/1.06      inference('cnf', [status(esa)], [t74_xboole_1])).
% 0.84/1.06  thf('19', plain,
% 0.84/1.06      (![X0 : $i]: (r1_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ sk_A @ X0))),
% 0.84/1.06      inference('sup-', [status(thm)], ['17', '18'])).
% 0.84/1.06  thf(t7_xboole_0, axiom,
% 0.84/1.06    (![A:$i]:
% 0.84/1.06     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.84/1.06          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.84/1.06  thf('20', plain,
% 0.84/1.06      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.84/1.06      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.84/1.06  thf(t4_xboole_0, axiom,
% 0.84/1.06    (![A:$i,B:$i]:
% 0.84/1.06     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.84/1.06            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.84/1.06       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.84/1.06            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.84/1.06  thf('21', plain,
% 0.84/1.06      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.84/1.06         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.84/1.06          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.84/1.06      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.84/1.06  thf('22', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]:
% 0.84/1.06         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.84/1.06      inference('sup-', [status(thm)], ['20', '21'])).
% 0.84/1.06  thf('23', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         ((k3_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ sk_A @ X0)) = (k1_xboole_0))),
% 0.84/1.06      inference('sup-', [status(thm)], ['19', '22'])).
% 0.84/1.06  thf(commutativity_k3_xboole_0, axiom,
% 0.84/1.06    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.84/1.06  thf('24', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.84/1.06      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.84/1.06  thf(t100_xboole_1, axiom,
% 0.84/1.06    (![A:$i,B:$i]:
% 0.84/1.06     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.84/1.06  thf('25', plain,
% 0.84/1.06      (![X12 : $i, X13 : $i]:
% 0.84/1.06         ((k4_xboole_0 @ X12 @ X13)
% 0.84/1.06           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.84/1.06      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.84/1.06  thf('26', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]:
% 0.84/1.06         ((k4_xboole_0 @ X0 @ X1)
% 0.84/1.06           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.84/1.06      inference('sup+', [status(thm)], ['24', '25'])).
% 0.84/1.06  thf('27', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         ((k4_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ sk_C_1)
% 0.84/1.06           = (k5_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ k1_xboole_0))),
% 0.84/1.06      inference('sup+', [status(thm)], ['23', '26'])).
% 0.84/1.06  thf(t49_xboole_1, axiom,
% 0.84/1.06    (![A:$i,B:$i,C:$i]:
% 0.84/1.06     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.84/1.06       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.84/1.06  thf('28', plain,
% 0.84/1.06      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.84/1.06         ((k3_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 0.84/1.06           = (k4_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ X21))),
% 0.84/1.06      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.84/1.06  thf(t5_boole, axiom,
% 0.84/1.06    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.84/1.06  thf('29', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.84/1.06      inference('cnf', [status(esa)], [t5_boole])).
% 0.84/1.06  thf('30', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C_1))
% 0.84/1.06           = (k3_xboole_0 @ sk_A @ X0))),
% 0.84/1.06      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.84/1.06  thf('31', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.84/1.06      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.84/1.06  thf('32', plain, (((k3_xboole_0 @ sk_B_1 @ sk_A) = (sk_A))),
% 0.84/1.06      inference('demod', [status(thm)], ['14', '30', '31'])).
% 0.84/1.06  thf('33', plain,
% 0.84/1.06      (![X29 : $i, X30 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X29 @ X30) @ X30)),
% 0.84/1.06      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.84/1.06  thf('34', plain,
% 0.84/1.06      (![X2 : $i, X3 : $i]:
% 0.84/1.06         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.84/1.06      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.84/1.06  thf('35', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.84/1.06      inference('sup-', [status(thm)], ['33', '34'])).
% 0.84/1.06  thf('36', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]:
% 0.84/1.06         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.84/1.06      inference('sup-', [status(thm)], ['20', '21'])).
% 0.84/1.06  thf('37', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]:
% 0.84/1.06         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.84/1.06      inference('sup-', [status(thm)], ['35', '36'])).
% 0.84/1.06  thf('38', plain,
% 0.84/1.06      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.84/1.06         ((k3_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 0.84/1.06           = (k4_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ X21))),
% 0.84/1.06      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.84/1.06  thf(l32_xboole_1, axiom,
% 0.84/1.06    (![A:$i,B:$i]:
% 0.84/1.06     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.84/1.06  thf('39', plain,
% 0.84/1.06      (![X9 : $i, X10 : $i]:
% 0.84/1.06         ((r1_tarski @ X9 @ X10) | ((k4_xboole_0 @ X9 @ X10) != (k1_xboole_0)))),
% 0.84/1.06      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.84/1.06  thf('40', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.06         (((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.84/1.06          | (r1_tarski @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 0.84/1.06      inference('sup-', [status(thm)], ['38', '39'])).
% 0.84/1.06  thf('41', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]:
% 0.84/1.06         (((k1_xboole_0) != (k1_xboole_0))
% 0.84/1.06          | (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.84/1.06      inference('sup-', [status(thm)], ['37', '40'])).
% 0.84/1.06  thf('42', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.84/1.06      inference('simplify', [status(thm)], ['41'])).
% 0.84/1.06  thf('43', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.84/1.06      inference('sup+', [status(thm)], ['32', '42'])).
% 0.84/1.06  thf('44', plain, ($false), inference('demod', [status(thm)], ['11', '43'])).
% 0.84/1.06  
% 0.84/1.06  % SZS output end Refutation
% 0.84/1.06  
% 0.84/1.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
