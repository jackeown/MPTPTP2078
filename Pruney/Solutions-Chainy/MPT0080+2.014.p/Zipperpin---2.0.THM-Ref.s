%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1Y8LjWvA4P

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:06 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 100 expanded)
%              Number of leaves         :   25 (  41 expanded)
%              Depth                    :   16
%              Number of atoms          :  495 ( 672 expanded)
%              Number of equality atoms :   42 (  56 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t73_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ C ) )
       => ( r1_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t73_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X29: $i,X30: $i] :
      ( r1_tarski @ X29 @ ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('8',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ X0 ) )
      | ( r1_tarski @ sk_A @ ( k2_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ) ),
    inference('sup+',[status(thm)],['1','13'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_xboole_0 @ X14 @ X13 )
        = X13 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X19 @ X20 ) @ X20 )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('19',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('22',plain,(
    ! [X28: $i] :
      ( r1_xboole_0 @ X28 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('23',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('27',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k4_xboole_0 @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('30',plain,(
    r1_xboole_0 @ sk_A @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('32',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C_2 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('33',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X26 @ X27 ) @ ( k4_xboole_0 @ X26 @ X27 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('34',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C_2 ) )
    = sk_A ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('36',plain,(
    ! [X15: $i] :
      ( ( k2_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_2 )
    = sk_A ),
    inference(demod,[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['18','25','28','29','38'])).

thf('40',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('41',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('42',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) )
      = ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('43',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('46',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('48',plain,(
    ! [X29: $i,X30: $i] :
      ( r1_tarski @ X29 @ ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['46','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['0','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1Y8LjWvA4P
% 0.14/0.36  % Computer   : n020.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 11:30:52 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.70/0.90  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.70/0.90  % Solved by: fo/fo7.sh
% 0.70/0.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.70/0.90  % done 981 iterations in 0.441s
% 0.70/0.90  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.70/0.90  % SZS output start Refutation
% 0.70/0.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.70/0.90  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.70/0.90  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.70/0.90  thf(sk_B_type, type, sk_B: $i).
% 0.70/0.90  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.70/0.90  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.70/0.90  thf(sk_A_type, type, sk_A: $i).
% 0.70/0.90  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.70/0.90  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.70/0.90  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.70/0.90  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.70/0.90  thf(t73_xboole_1, conjecture,
% 0.70/0.90    (![A:$i,B:$i,C:$i]:
% 0.70/0.90     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.70/0.90       ( r1_tarski @ A @ B ) ))).
% 0.70/0.90  thf(zf_stmt_0, negated_conjecture,
% 0.70/0.90    (~( ![A:$i,B:$i,C:$i]:
% 0.70/0.90        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 0.70/0.90            ( r1_xboole_0 @ A @ C ) ) =>
% 0.70/0.90          ( r1_tarski @ A @ B ) ) )),
% 0.70/0.90    inference('cnf.neg', [status(esa)], [t73_xboole_1])).
% 0.70/0.90  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.70/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.90  thf(commutativity_k2_xboole_0, axiom,
% 0.70/0.90    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.70/0.90  thf('1', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.70/0.90      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.70/0.90  thf(d3_tarski, axiom,
% 0.70/0.90    (![A:$i,B:$i]:
% 0.70/0.90     ( ( r1_tarski @ A @ B ) <=>
% 0.70/0.90       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.70/0.90  thf('2', plain,
% 0.70/0.90      (![X3 : $i, X5 : $i]:
% 0.70/0.90         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.70/0.90      inference('cnf', [status(esa)], [d3_tarski])).
% 0.70/0.90  thf('3', plain, ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.70/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.90  thf('4', plain,
% 0.70/0.90      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.70/0.90         (~ (r2_hidden @ X2 @ X3)
% 0.70/0.90          | (r2_hidden @ X2 @ X4)
% 0.70/0.90          | ~ (r1_tarski @ X3 @ X4))),
% 0.70/0.90      inference('cnf', [status(esa)], [d3_tarski])).
% 0.70/0.90  thf('5', plain,
% 0.70/0.90      (![X0 : $i]:
% 0.70/0.90         ((r2_hidden @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.70/0.90          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.70/0.90      inference('sup-', [status(thm)], ['3', '4'])).
% 0.70/0.90  thf('6', plain,
% 0.70/0.90      (![X0 : $i]:
% 0.70/0.90         ((r1_tarski @ sk_A @ X0)
% 0.70/0.90          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 0.70/0.90      inference('sup-', [status(thm)], ['2', '5'])).
% 0.70/0.90  thf(t7_xboole_1, axiom,
% 0.70/0.90    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.70/0.90  thf('7', plain,
% 0.70/0.90      (![X29 : $i, X30 : $i]: (r1_tarski @ X29 @ (k2_xboole_0 @ X29 @ X30))),
% 0.70/0.90      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.70/0.90  thf('8', plain,
% 0.70/0.90      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.70/0.90         (~ (r2_hidden @ X2 @ X3)
% 0.70/0.90          | (r2_hidden @ X2 @ X4)
% 0.70/0.90          | ~ (r1_tarski @ X3 @ X4))),
% 0.70/0.90      inference('cnf', [status(esa)], [d3_tarski])).
% 0.70/0.90  thf('9', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.90         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X1))),
% 0.70/0.90      inference('sup-', [status(thm)], ['7', '8'])).
% 0.70/0.90  thf('10', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]:
% 0.70/0.90         ((r1_tarski @ sk_A @ X0)
% 0.70/0.90          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ 
% 0.70/0.90             (k2_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ X1)))),
% 0.70/0.90      inference('sup-', [status(thm)], ['6', '9'])).
% 0.70/0.90  thf('11', plain,
% 0.70/0.90      (![X3 : $i, X5 : $i]:
% 0.70/0.90         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.70/0.90      inference('cnf', [status(esa)], [d3_tarski])).
% 0.70/0.90  thf('12', plain,
% 0.70/0.90      (![X0 : $i]:
% 0.70/0.90         ((r1_tarski @ sk_A @ 
% 0.70/0.90           (k2_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ X0))
% 0.70/0.90          | (r1_tarski @ sk_A @ 
% 0.70/0.90             (k2_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ X0)))),
% 0.70/0.90      inference('sup-', [status(thm)], ['10', '11'])).
% 0.70/0.90  thf('13', plain,
% 0.70/0.90      (![X0 : $i]:
% 0.70/0.90         (r1_tarski @ sk_A @ (k2_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ X0))),
% 0.70/0.90      inference('simplify', [status(thm)], ['12'])).
% 0.70/0.90  thf('14', plain,
% 0.70/0.90      (![X0 : $i]:
% 0.70/0.90         (r1_tarski @ sk_A @ (k2_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 0.70/0.90      inference('sup+', [status(thm)], ['1', '13'])).
% 0.70/0.90  thf(t12_xboole_1, axiom,
% 0.70/0.90    (![A:$i,B:$i]:
% 0.70/0.90     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.70/0.90  thf('15', plain,
% 0.70/0.90      (![X13 : $i, X14 : $i]:
% 0.70/0.90         (((k2_xboole_0 @ X14 @ X13) = (X13)) | ~ (r1_tarski @ X14 @ X13))),
% 0.70/0.90      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.70/0.90  thf('16', plain,
% 0.70/0.90      (![X0 : $i]:
% 0.70/0.90         ((k2_xboole_0 @ sk_A @ 
% 0.70/0.90           (k2_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2)))
% 0.70/0.90           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 0.70/0.90      inference('sup-', [status(thm)], ['14', '15'])).
% 0.70/0.90  thf(t40_xboole_1, axiom,
% 0.70/0.90    (![A:$i,B:$i]:
% 0.70/0.90     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.70/0.90  thf('17', plain,
% 0.70/0.90      (![X19 : $i, X20 : $i]:
% 0.70/0.90         ((k4_xboole_0 @ (k2_xboole_0 @ X19 @ X20) @ X20)
% 0.70/0.90           = (k4_xboole_0 @ X19 @ X20))),
% 0.70/0.90      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.70/0.90  thf('18', plain,
% 0.70/0.90      (![X0 : $i]:
% 0.70/0.90         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2)) @ 
% 0.70/0.90           (k2_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2)))
% 0.70/0.90           = (k4_xboole_0 @ sk_A @ 
% 0.70/0.90              (k2_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2))))),
% 0.70/0.90      inference('sup+', [status(thm)], ['16', '17'])).
% 0.70/0.90  thf(t3_boole, axiom,
% 0.70/0.90    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.70/0.90  thf('19', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.70/0.90      inference('cnf', [status(esa)], [t3_boole])).
% 0.70/0.90  thf(t48_xboole_1, axiom,
% 0.70/0.90    (![A:$i,B:$i]:
% 0.70/0.90     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.70/0.90  thf('20', plain,
% 0.70/0.90      (![X24 : $i, X25 : $i]:
% 0.70/0.90         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 0.70/0.90           = (k3_xboole_0 @ X24 @ X25))),
% 0.70/0.90      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.70/0.90  thf('21', plain,
% 0.70/0.90      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.70/0.90      inference('sup+', [status(thm)], ['19', '20'])).
% 0.70/0.90  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.70/0.90  thf('22', plain, (![X28 : $i]: (r1_xboole_0 @ X28 @ k1_xboole_0)),
% 0.70/0.90      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.70/0.90  thf(d7_xboole_0, axiom,
% 0.70/0.90    (![A:$i,B:$i]:
% 0.70/0.90     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.70/0.90       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.70/0.90  thf('23', plain,
% 0.70/0.90      (![X6 : $i, X7 : $i]:
% 0.70/0.90         (((k3_xboole_0 @ X6 @ X7) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 0.70/0.90      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.70/0.90  thf('24', plain,
% 0.70/0.90      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.70/0.90      inference('sup-', [status(thm)], ['22', '23'])).
% 0.70/0.90  thf('25', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.70/0.90      inference('demod', [status(thm)], ['21', '24'])).
% 0.70/0.90  thf('26', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.70/0.90      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.70/0.90  thf(t41_xboole_1, axiom,
% 0.70/0.90    (![A:$i,B:$i,C:$i]:
% 0.70/0.90     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.70/0.90       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.70/0.90  thf('27', plain,
% 0.70/0.90      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.70/0.90         ((k4_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ X23)
% 0.70/0.90           = (k4_xboole_0 @ X21 @ (k2_xboole_0 @ X22 @ X23)))),
% 0.70/0.90      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.70/0.90  thf('28', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.90         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 0.70/0.90           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.70/0.90      inference('sup+', [status(thm)], ['26', '27'])).
% 0.70/0.90  thf('29', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.90         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 0.70/0.90           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.70/0.90      inference('sup+', [status(thm)], ['26', '27'])).
% 0.70/0.90  thf('30', plain, ((r1_xboole_0 @ sk_A @ sk_C_2)),
% 0.70/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.90  thf('31', plain,
% 0.70/0.90      (![X6 : $i, X7 : $i]:
% 0.70/0.90         (((k3_xboole_0 @ X6 @ X7) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 0.70/0.90      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.70/0.90  thf('32', plain, (((k3_xboole_0 @ sk_A @ sk_C_2) = (k1_xboole_0))),
% 0.70/0.90      inference('sup-', [status(thm)], ['30', '31'])).
% 0.70/0.90  thf(t51_xboole_1, axiom,
% 0.70/0.90    (![A:$i,B:$i]:
% 0.70/0.90     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.70/0.90       ( A ) ))).
% 0.70/0.90  thf('33', plain,
% 0.70/0.90      (![X26 : $i, X27 : $i]:
% 0.70/0.90         ((k2_xboole_0 @ (k3_xboole_0 @ X26 @ X27) @ (k4_xboole_0 @ X26 @ X27))
% 0.70/0.90           = (X26))),
% 0.70/0.90      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.70/0.90  thf('34', plain,
% 0.70/0.90      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C_2)) = (sk_A))),
% 0.70/0.90      inference('sup+', [status(thm)], ['32', '33'])).
% 0.70/0.90  thf('35', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.70/0.90      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.70/0.90  thf(t1_boole, axiom,
% 0.70/0.90    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.70/0.90  thf('36', plain, (![X15 : $i]: ((k2_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.70/0.90      inference('cnf', [status(esa)], [t1_boole])).
% 0.70/0.90  thf('37', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.70/0.90      inference('sup+', [status(thm)], ['35', '36'])).
% 0.70/0.90  thf('38', plain, (((k4_xboole_0 @ sk_A @ sk_C_2) = (sk_A))),
% 0.70/0.90      inference('demod', [status(thm)], ['34', '37'])).
% 0.70/0.90  thf('39', plain,
% 0.70/0.90      (![X0 : $i]:
% 0.70/0.90         ((k1_xboole_0) = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ X0))),
% 0.70/0.90      inference('demod', [status(thm)], ['18', '25', '28', '29', '38'])).
% 0.70/0.90  thf('40', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.70/0.90      inference('cnf', [status(esa)], [t3_boole])).
% 0.70/0.90  thf('41', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.70/0.90      inference('sup+', [status(thm)], ['39', '40'])).
% 0.70/0.90  thf(t39_xboole_1, axiom,
% 0.70/0.90    (![A:$i,B:$i]:
% 0.70/0.90     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.70/0.90  thf('42', plain,
% 0.70/0.90      (![X16 : $i, X17 : $i]:
% 0.70/0.90         ((k2_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16))
% 0.70/0.90           = (k2_xboole_0 @ X16 @ X17))),
% 0.70/0.90      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.70/0.90  thf('43', plain,
% 0.70/0.90      (((k2_xboole_0 @ sk_B @ k1_xboole_0) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.70/0.90      inference('sup+', [status(thm)], ['41', '42'])).
% 0.70/0.90  thf('44', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.70/0.90      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.70/0.90  thf('45', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.70/0.90      inference('sup+', [status(thm)], ['35', '36'])).
% 0.70/0.90  thf('46', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.70/0.90      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.70/0.90  thf('47', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.70/0.90      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.70/0.90  thf('48', plain,
% 0.70/0.90      (![X29 : $i, X30 : $i]: (r1_tarski @ X29 @ (k2_xboole_0 @ X29 @ X30))),
% 0.70/0.90      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.70/0.90  thf('49', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.70/0.90      inference('sup+', [status(thm)], ['47', '48'])).
% 0.70/0.90  thf('50', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.70/0.90      inference('sup+', [status(thm)], ['46', '49'])).
% 0.70/0.90  thf('51', plain, ($false), inference('demod', [status(thm)], ['0', '50'])).
% 0.70/0.90  
% 0.70/0.90  % SZS output end Refutation
% 0.70/0.90  
% 0.70/0.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
