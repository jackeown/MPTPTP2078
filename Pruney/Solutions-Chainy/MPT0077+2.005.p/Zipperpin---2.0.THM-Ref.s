%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WwlCHzS1h2

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:49 EST 2020

% Result     : Theorem 4.37s
% Output     : Refutation 4.37s
% Verified   : 
% Statistics : Number of formulae       :  237 (3656 expanded)
%              Number of leaves         :   21 (1230 expanded)
%              Depth                    :   23
%              Number of atoms          : 1965 (29106 expanded)
%              Number of equality atoms :  176 (3184 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t70_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
                & ( r1_xboole_0 @ A @ C ) )
            & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
        & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
            & ( r1_xboole_0 @ A @ B )
            & ( r1_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t70_xboole_1])).

thf('0',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C_2 )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_B )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( r1_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( r1_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C_2 )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('5',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C_2 )
   <= ( r1_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference(split,[status(esa)],['2'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('7',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_C_2 )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('9',plain,
    ( ( ( k3_xboole_0 @ sk_C_2 @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,
    ( ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_C_2 @ sk_A ) )
      = ( k2_xboole_0 @ sk_C_2 @ ( k4_xboole_0 @ sk_C_2 @ sk_A ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['9','15'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('17',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X18 @ X19 ) @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k4_xboole_0 @ sk_C_2 @ sk_A )
      = ( k2_xboole_0 @ sk_C_2 @ ( k4_xboole_0 @ sk_C_2 @ sk_A ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference(demod,[status(thm)],['16','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('26',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X18 @ X19 ) @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('33',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('35',plain,(
    ! [X25: $i] :
      ( r1_xboole_0 @ X25 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('36',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','37'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('39',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k4_xboole_0 @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('40',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('47',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['42','47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['31','49'])).

thf('51',plain,
    ( ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_C_2 @ sk_A ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_C_2 @ sk_A ) @ sk_C_2 ) )
      = sk_C_2 )
   <= ( r1_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['24','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('54',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k4_xboole_0 @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X18 @ X19 ) @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('60',plain,
    ( ( ( k4_xboole_0 @ sk_C_2 @ sk_A )
      = sk_C_2 )
   <= ( r1_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference(demod,[status(thm)],['51','58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['31','49'])).

thf('62',plain,
    ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) @ sk_C_2 )
      = sk_A )
   <= ( r1_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('65',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_C_2 )
      = sk_A )
   <= ( r1_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['66'])).

thf('68',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('69',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('71',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('73',plain,
    ( ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_A ) )
      = ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_A ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('75',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_A )
      = ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_A ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['31','49'])).

thf('77',plain,
    ( ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_A ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_A ) @ sk_B ) )
      = sk_B )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('79',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('80',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_A )
      = sk_B )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['31','49'])).

thf('82',plain,
    ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_B )
      = sk_A )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('85',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k4_xboole_0 @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('88',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('91',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k4_xboole_0 @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('97',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['86','101'])).

thf('103',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( k2_xboole_0 @ sk_B @ X0 ) @ ( k4_xboole_0 @ sk_A @ X0 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['85','102'])).

thf('104',plain,
    ( ( r1_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ sk_A )
   <= ( ( r1_xboole_0 @ sk_A @ sk_B )
      & ( r1_xboole_0 @ sk_A @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['65','103'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('105',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C_1 @ X12 @ X11 ) @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('106',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('107',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k3_xboole_0 @ X11 @ X14 ) )
      | ~ ( r1_xboole_0 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['105','108'])).

thf('110',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
   <= ( ( r1_xboole_0 @ sk_A @ sk_B )
      & ( r1_xboole_0 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['104','109'])).

thf('111',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
   <= ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('112',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C_2 )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('114',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['66'])).

thf('115',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('116',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('118',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,
    ( ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
      = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['116','119'])).

thf('121',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('122',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k4_xboole_0 @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('123',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C_2 ) ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('124',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C_2 ) ) )
   <= ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      & ( r1_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['113','123'])).

thf('125',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('126',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['125','128'])).

thf('130',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C_2 ) )
      = k1_xboole_0 )
   <= ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      & ( r1_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['124','129'])).

thf('131',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('132',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('133',plain,
    ( ( ( k3_xboole_0 @ sk_C_2 @ sk_A )
      = k1_xboole_0 )
   <= ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      & ( r1_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['130','131','132'])).

thf('134',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('135',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ sk_C_2 ) )
   <= ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      & ( r1_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['133','136'])).

thf('138',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C_2 )
   <= ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      & ( r1_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C_2 )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('140',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C_2 )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['3','4','112','140'])).

thf('142',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','141'])).

thf('143',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('144',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['66'])).

thf('145',plain,(
    r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference('sat_resolution*',[status(thm)],['3','4','112','140','144'])).

thf('146',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['143','145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('149',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('151',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C_2 ) @ sk_B ) )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C_2 ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['146','151'])).

thf('153',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_C_2 )
      = sk_A )
   <= ( r1_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('154',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('155',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C_1 @ X12 @ X11 ) @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['154','155'])).

thf('157',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C_2 ) ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('158',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('159',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('160',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('162',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('165',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('170',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('171',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('173',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['171','172','173'])).

thf('175',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k3_xboole_0 @ X11 @ X14 ) )
      | ~ ( r1_xboole_0 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('176',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['168','176'])).

thf('178',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['163','177'])).

thf('179',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      | ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['162','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('181',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('184',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['184'])).

thf('186',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('187',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('188',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('190',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('192',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['179','185','190','191'])).

thf('193',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['159','192'])).

thf('194',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['158','193'])).

thf('195',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_C_2 @ sk_A ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['157','194'])).

thf('196',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C_2 )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['156','195'])).

thf('197',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C_2 )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('198',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C_2 )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,(
    r1_xboole_0 @ sk_A @ sk_C_2 ),
    inference('sat_resolution*',[status(thm)],['3','4','112','140','144','198'])).

thf('200',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_2 )
    = sk_A ),
    inference(simpl_trail,[status(thm)],['153','199'])).

thf('201',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('202',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_2 )
    = sk_A ),
    inference(simpl_trail,[status(thm)],['153','199'])).

thf('203',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('204',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('205',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['203','204'])).

thf('206',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('207',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['205','206'])).

thf('208',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['152','200','201','202','207'])).

thf('209',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('210',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('211',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['209','210'])).

thf('212',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['211'])).

thf('213',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['208','212'])).

thf('214',plain,(
    $false ),
    inference(demod,[status(thm)],['142','213'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WwlCHzS1h2
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:26:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 4.37/4.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.37/4.57  % Solved by: fo/fo7.sh
% 4.37/4.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.37/4.57  % done 3687 iterations in 4.102s
% 4.37/4.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.37/4.57  % SZS output start Refutation
% 4.37/4.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.37/4.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.37/4.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.37/4.57  thf(sk_B_type, type, sk_B: $i).
% 4.37/4.57  thf(sk_C_2_type, type, sk_C_2: $i).
% 4.37/4.57  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 4.37/4.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.37/4.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.37/4.57  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 4.37/4.57  thf(sk_A_type, type, sk_A: $i).
% 4.37/4.57  thf(t70_xboole_1, conjecture,
% 4.37/4.57    (![A:$i,B:$i,C:$i]:
% 4.37/4.57     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 4.37/4.57            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 4.37/4.57       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 4.37/4.57            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 4.37/4.57  thf(zf_stmt_0, negated_conjecture,
% 4.37/4.57    (~( ![A:$i,B:$i,C:$i]:
% 4.37/4.57        ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 4.37/4.57               ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 4.37/4.57          ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 4.37/4.57               ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ) )),
% 4.37/4.57    inference('cnf.neg', [status(esa)], [t70_xboole_1])).
% 4.37/4.57  thf('0', plain,
% 4.37/4.57      ((~ (r1_xboole_0 @ sk_A @ sk_C_2)
% 4.37/4.57        | ~ (r1_xboole_0 @ sk_A @ sk_B)
% 4.37/4.57        | ~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 4.37/4.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.57  thf('1', plain,
% 4.37/4.57      ((~ (r1_xboole_0 @ sk_A @ sk_B)) <= (~ ((r1_xboole_0 @ sk_A @ sk_B)))),
% 4.37/4.57      inference('split', [status(esa)], ['0'])).
% 4.37/4.57  thf('2', plain,
% 4.37/4.57      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 4.37/4.57        | (r1_xboole_0 @ sk_A @ sk_C_2))),
% 4.37/4.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.57  thf('3', plain,
% 4.37/4.57      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))) | 
% 4.37/4.57       ((r1_xboole_0 @ sk_A @ sk_C_2))),
% 4.37/4.57      inference('split', [status(esa)], ['2'])).
% 4.37/4.57  thf('4', plain,
% 4.37/4.57      (~ ((r1_xboole_0 @ sk_A @ sk_B)) | ~ ((r1_xboole_0 @ sk_A @ sk_C_2)) | 
% 4.37/4.57       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 4.37/4.57      inference('split', [status(esa)], ['0'])).
% 4.37/4.57  thf('5', plain,
% 4.37/4.57      (((r1_xboole_0 @ sk_A @ sk_C_2)) <= (((r1_xboole_0 @ sk_A @ sk_C_2)))),
% 4.37/4.57      inference('split', [status(esa)], ['2'])).
% 4.37/4.57  thf(d7_xboole_0, axiom,
% 4.37/4.57    (![A:$i,B:$i]:
% 4.37/4.57     ( ( r1_xboole_0 @ A @ B ) <=>
% 4.37/4.57       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 4.37/4.57  thf('6', plain,
% 4.37/4.57      (![X4 : $i, X5 : $i]:
% 4.37/4.57         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 4.37/4.57      inference('cnf', [status(esa)], [d7_xboole_0])).
% 4.37/4.57  thf('7', plain,
% 4.37/4.57      ((((k3_xboole_0 @ sk_A @ sk_C_2) = (k1_xboole_0)))
% 4.37/4.57         <= (((r1_xboole_0 @ sk_A @ sk_C_2)))),
% 4.37/4.57      inference('sup-', [status(thm)], ['5', '6'])).
% 4.37/4.57  thf(commutativity_k3_xboole_0, axiom,
% 4.37/4.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 4.37/4.57  thf('8', plain,
% 4.37/4.57      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 4.37/4.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.37/4.57  thf('9', plain,
% 4.37/4.57      ((((k3_xboole_0 @ sk_C_2 @ sk_A) = (k1_xboole_0)))
% 4.37/4.57         <= (((r1_xboole_0 @ sk_A @ sk_C_2)))),
% 4.37/4.57      inference('demod', [status(thm)], ['7', '8'])).
% 4.37/4.57  thf(t48_xboole_1, axiom,
% 4.37/4.57    (![A:$i,B:$i]:
% 4.37/4.57     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 4.37/4.57  thf('10', plain,
% 4.37/4.57      (![X23 : $i, X24 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 4.37/4.57           = (k3_xboole_0 @ X23 @ X24))),
% 4.37/4.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.37/4.57  thf(t39_xboole_1, axiom,
% 4.37/4.57    (![A:$i,B:$i]:
% 4.37/4.57     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 4.37/4.57  thf('11', plain,
% 4.37/4.57      (![X15 : $i, X16 : $i]:
% 4.37/4.57         ((k2_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15))
% 4.37/4.57           = (k2_xboole_0 @ X15 @ X16))),
% 4.37/4.57      inference('cnf', [status(esa)], [t39_xboole_1])).
% 4.37/4.57  thf('12', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]:
% 4.37/4.57         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 4.37/4.57           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 4.37/4.57      inference('sup+', [status(thm)], ['10', '11'])).
% 4.37/4.57  thf(commutativity_k2_xboole_0, axiom,
% 4.37/4.57    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 4.37/4.57  thf('13', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.37/4.57      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.37/4.57  thf('14', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.37/4.57      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.37/4.57  thf('15', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]:
% 4.37/4.57         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 4.37/4.57           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 4.37/4.57      inference('demod', [status(thm)], ['12', '13', '14'])).
% 4.37/4.57  thf('16', plain,
% 4.37/4.57      ((((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_C_2 @ sk_A))
% 4.37/4.57          = (k2_xboole_0 @ sk_C_2 @ (k4_xboole_0 @ sk_C_2 @ sk_A))))
% 4.37/4.57         <= (((r1_xboole_0 @ sk_A @ sk_C_2)))),
% 4.37/4.57      inference('sup+', [status(thm)], ['9', '15'])).
% 4.37/4.57  thf(t3_boole, axiom,
% 4.37/4.57    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 4.37/4.57  thf('17', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 4.37/4.57      inference('cnf', [status(esa)], [t3_boole])).
% 4.37/4.57  thf(t40_xboole_1, axiom,
% 4.37/4.57    (![A:$i,B:$i]:
% 4.37/4.57     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 4.37/4.57  thf('18', plain,
% 4.37/4.57      (![X18 : $i, X19 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ (k2_xboole_0 @ X18 @ X19) @ X19)
% 4.37/4.57           = (k4_xboole_0 @ X18 @ X19))),
% 4.37/4.57      inference('cnf', [status(esa)], [t40_xboole_1])).
% 4.37/4.57  thf('19', plain,
% 4.37/4.57      (![X0 : $i]:
% 4.37/4.57         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 4.37/4.57      inference('sup+', [status(thm)], ['17', '18'])).
% 4.37/4.57  thf('20', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 4.37/4.57      inference('cnf', [status(esa)], [t3_boole])).
% 4.37/4.57  thf('21', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 4.37/4.57      inference('demod', [status(thm)], ['19', '20'])).
% 4.37/4.57  thf('22', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.37/4.57      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.37/4.57  thf('23', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 4.37/4.57      inference('sup+', [status(thm)], ['21', '22'])).
% 4.37/4.57  thf('24', plain,
% 4.37/4.57      ((((k4_xboole_0 @ sk_C_2 @ sk_A)
% 4.37/4.57          = (k2_xboole_0 @ sk_C_2 @ (k4_xboole_0 @ sk_C_2 @ sk_A))))
% 4.37/4.57         <= (((r1_xboole_0 @ sk_A @ sk_C_2)))),
% 4.37/4.57      inference('demod', [status(thm)], ['16', '23'])).
% 4.37/4.57  thf('25', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.37/4.57      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.37/4.57  thf('26', plain,
% 4.37/4.57      (![X18 : $i, X19 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ (k2_xboole_0 @ X18 @ X19) @ X19)
% 4.37/4.57           = (k4_xboole_0 @ X18 @ X19))),
% 4.37/4.57      inference('cnf', [status(esa)], [t40_xboole_1])).
% 4.37/4.57  thf('27', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 4.37/4.57           = (k4_xboole_0 @ X0 @ X1))),
% 4.37/4.57      inference('sup+', [status(thm)], ['25', '26'])).
% 4.37/4.57  thf('28', plain,
% 4.37/4.57      (![X23 : $i, X24 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 4.37/4.57           = (k3_xboole_0 @ X23 @ X24))),
% 4.37/4.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.37/4.57  thf('29', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 4.37/4.57           = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 4.37/4.57      inference('sup+', [status(thm)], ['27', '28'])).
% 4.37/4.57  thf('30', plain,
% 4.37/4.57      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 4.37/4.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.37/4.57  thf('31', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 4.37/4.57           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 4.37/4.57      inference('demod', [status(thm)], ['29', '30'])).
% 4.37/4.57  thf('32', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 4.37/4.57      inference('cnf', [status(esa)], [t3_boole])).
% 4.37/4.57  thf('33', plain,
% 4.37/4.57      (![X23 : $i, X24 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 4.37/4.57           = (k3_xboole_0 @ X23 @ X24))),
% 4.37/4.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.37/4.57  thf('34', plain,
% 4.37/4.57      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 4.37/4.57      inference('sup+', [status(thm)], ['32', '33'])).
% 4.37/4.57  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 4.37/4.57  thf('35', plain, (![X25 : $i]: (r1_xboole_0 @ X25 @ k1_xboole_0)),
% 4.37/4.57      inference('cnf', [status(esa)], [t65_xboole_1])).
% 4.37/4.57  thf('36', plain,
% 4.37/4.57      (![X4 : $i, X5 : $i]:
% 4.37/4.57         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 4.37/4.57      inference('cnf', [status(esa)], [d7_xboole_0])).
% 4.37/4.57  thf('37', plain,
% 4.37/4.57      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 4.37/4.57      inference('sup-', [status(thm)], ['35', '36'])).
% 4.37/4.57  thf('38', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 4.37/4.57      inference('demod', [status(thm)], ['34', '37'])).
% 4.37/4.57  thf(t41_xboole_1, axiom,
% 4.37/4.57    (![A:$i,B:$i,C:$i]:
% 4.37/4.57     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 4.37/4.57       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 4.37/4.57  thf('39', plain,
% 4.37/4.57      (![X20 : $i, X21 : $i, X22 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ X22)
% 4.37/4.57           = (k4_xboole_0 @ X20 @ (k2_xboole_0 @ X21 @ X22)))),
% 4.37/4.57      inference('cnf', [status(esa)], [t41_xboole_1])).
% 4.37/4.57  thf('40', plain,
% 4.37/4.57      (![X23 : $i, X24 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 4.37/4.57           = (k3_xboole_0 @ X23 @ X24))),
% 4.37/4.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.37/4.57  thf('41', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 4.37/4.57           = (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 4.37/4.57      inference('sup+', [status(thm)], ['39', '40'])).
% 4.37/4.57  thf('42', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))
% 4.37/4.57           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 4.37/4.57      inference('sup+', [status(thm)], ['38', '41'])).
% 4.37/4.57  thf('43', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 4.37/4.57      inference('demod', [status(thm)], ['19', '20'])).
% 4.37/4.57  thf('44', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 4.37/4.57           = (k4_xboole_0 @ X0 @ X1))),
% 4.37/4.57      inference('sup+', [status(thm)], ['25', '26'])).
% 4.37/4.57  thf('45', plain,
% 4.37/4.57      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 4.37/4.57      inference('sup+', [status(thm)], ['43', '44'])).
% 4.37/4.57  thf('46', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 4.37/4.57      inference('demod', [status(thm)], ['34', '37'])).
% 4.37/4.57  thf('47', plain,
% 4.37/4.57      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 4.37/4.57      inference('demod', [status(thm)], ['45', '46'])).
% 4.37/4.57  thf('48', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 4.37/4.57      inference('cnf', [status(esa)], [t3_boole])).
% 4.37/4.57  thf('49', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]:
% 4.37/4.57         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 4.37/4.57      inference('demod', [status(thm)], ['42', '47', '48'])).
% 4.37/4.57  thf('50', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 4.37/4.57           = (X0))),
% 4.37/4.57      inference('demod', [status(thm)], ['31', '49'])).
% 4.37/4.57  thf('51', plain,
% 4.37/4.57      ((((k4_xboole_0 @ (k4_xboole_0 @ sk_C_2 @ sk_A) @ 
% 4.37/4.57          (k4_xboole_0 @ (k4_xboole_0 @ sk_C_2 @ sk_A) @ sk_C_2)) = (sk_C_2)))
% 4.37/4.57         <= (((r1_xboole_0 @ sk_A @ sk_C_2)))),
% 4.37/4.57      inference('sup+', [status(thm)], ['24', '50'])).
% 4.37/4.57  thf('52', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 4.37/4.57      inference('demod', [status(thm)], ['34', '37'])).
% 4.37/4.57  thf('53', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.37/4.57      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.37/4.57  thf('54', plain,
% 4.37/4.57      (![X20 : $i, X21 : $i, X22 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ X22)
% 4.37/4.57           = (k4_xboole_0 @ X20 @ (k2_xboole_0 @ X21 @ X22)))),
% 4.37/4.57      inference('cnf', [status(esa)], [t41_xboole_1])).
% 4.37/4.57  thf('55', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 4.37/4.57           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 4.37/4.57      inference('sup+', [status(thm)], ['53', '54'])).
% 4.37/4.57  thf('56', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X1) @ X0)
% 4.37/4.57           = (k1_xboole_0))),
% 4.37/4.57      inference('sup+', [status(thm)], ['52', '55'])).
% 4.37/4.57  thf('57', plain,
% 4.37/4.57      (![X18 : $i, X19 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ (k2_xboole_0 @ X18 @ X19) @ X19)
% 4.37/4.57           = (k4_xboole_0 @ X18 @ X19))),
% 4.37/4.57      inference('cnf', [status(esa)], [t40_xboole_1])).
% 4.37/4.57  thf('58', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 4.37/4.57      inference('demod', [status(thm)], ['56', '57'])).
% 4.37/4.57  thf('59', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 4.37/4.57      inference('cnf', [status(esa)], [t3_boole])).
% 4.37/4.57  thf('60', plain,
% 4.37/4.57      ((((k4_xboole_0 @ sk_C_2 @ sk_A) = (sk_C_2)))
% 4.37/4.57         <= (((r1_xboole_0 @ sk_A @ sk_C_2)))),
% 4.37/4.57      inference('demod', [status(thm)], ['51', '58', '59'])).
% 4.37/4.57  thf('61', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 4.37/4.57           = (X0))),
% 4.37/4.57      inference('demod', [status(thm)], ['31', '49'])).
% 4.37/4.57  thf('62', plain,
% 4.37/4.57      ((((k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_2) @ sk_C_2) = (sk_A)))
% 4.37/4.57         <= (((r1_xboole_0 @ sk_A @ sk_C_2)))),
% 4.37/4.57      inference('sup+', [status(thm)], ['60', '61'])).
% 4.37/4.57  thf('63', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.37/4.57      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.37/4.57  thf('64', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 4.37/4.57           = (k4_xboole_0 @ X0 @ X1))),
% 4.37/4.57      inference('sup+', [status(thm)], ['25', '26'])).
% 4.37/4.57  thf('65', plain,
% 4.37/4.57      ((((k4_xboole_0 @ sk_A @ sk_C_2) = (sk_A)))
% 4.37/4.57         <= (((r1_xboole_0 @ sk_A @ sk_C_2)))),
% 4.37/4.57      inference('demod', [status(thm)], ['62', '63', '64'])).
% 4.37/4.57  thf('66', plain,
% 4.37/4.57      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 4.37/4.57        | (r1_xboole_0 @ sk_A @ sk_B))),
% 4.37/4.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.57  thf('67', plain,
% 4.37/4.57      (((r1_xboole_0 @ sk_A @ sk_B)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 4.37/4.57      inference('split', [status(esa)], ['66'])).
% 4.37/4.57  thf('68', plain,
% 4.37/4.57      (![X4 : $i, X5 : $i]:
% 4.37/4.57         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 4.37/4.57      inference('cnf', [status(esa)], [d7_xboole_0])).
% 4.37/4.57  thf('69', plain,
% 4.37/4.57      ((((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))
% 4.37/4.57         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 4.37/4.57      inference('sup-', [status(thm)], ['67', '68'])).
% 4.37/4.57  thf('70', plain,
% 4.37/4.57      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 4.37/4.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.37/4.57  thf('71', plain,
% 4.37/4.57      ((((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0)))
% 4.37/4.57         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 4.37/4.57      inference('demod', [status(thm)], ['69', '70'])).
% 4.37/4.57  thf('72', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]:
% 4.37/4.57         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 4.37/4.57           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 4.37/4.57      inference('demod', [status(thm)], ['12', '13', '14'])).
% 4.37/4.57  thf('73', plain,
% 4.37/4.57      ((((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A))
% 4.37/4.57          = (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_A))))
% 4.37/4.57         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 4.37/4.57      inference('sup+', [status(thm)], ['71', '72'])).
% 4.37/4.57  thf('74', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 4.37/4.57      inference('sup+', [status(thm)], ['21', '22'])).
% 4.37/4.57  thf('75', plain,
% 4.37/4.57      ((((k4_xboole_0 @ sk_B @ sk_A)
% 4.37/4.57          = (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_A))))
% 4.37/4.57         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 4.37/4.57      inference('demod', [status(thm)], ['73', '74'])).
% 4.37/4.57  thf('76', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 4.37/4.57           = (X0))),
% 4.37/4.57      inference('demod', [status(thm)], ['31', '49'])).
% 4.37/4.57  thf('77', plain,
% 4.37/4.57      ((((k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A) @ 
% 4.37/4.57          (k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A) @ sk_B)) = (sk_B)))
% 4.37/4.57         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 4.37/4.57      inference('sup+', [status(thm)], ['75', '76'])).
% 4.37/4.57  thf('78', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 4.37/4.57      inference('demod', [status(thm)], ['56', '57'])).
% 4.37/4.57  thf('79', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 4.37/4.57      inference('cnf', [status(esa)], [t3_boole])).
% 4.37/4.57  thf('80', plain,
% 4.37/4.57      ((((k4_xboole_0 @ sk_B @ sk_A) = (sk_B)))
% 4.37/4.57         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 4.37/4.57      inference('demod', [status(thm)], ['77', '78', '79'])).
% 4.37/4.57  thf('81', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 4.37/4.57           = (X0))),
% 4.37/4.57      inference('demod', [status(thm)], ['31', '49'])).
% 4.37/4.57  thf('82', plain,
% 4.37/4.57      ((((k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_B) = (sk_A)))
% 4.37/4.57         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 4.37/4.57      inference('sup+', [status(thm)], ['80', '81'])).
% 4.37/4.57  thf('83', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.37/4.57      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.37/4.57  thf('84', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 4.37/4.57           = (k4_xboole_0 @ X0 @ X1))),
% 4.37/4.57      inference('sup+', [status(thm)], ['25', '26'])).
% 4.37/4.57  thf('85', plain,
% 4.37/4.57      ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))
% 4.37/4.57         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 4.37/4.57      inference('demod', [status(thm)], ['82', '83', '84'])).
% 4.37/4.57  thf('86', plain,
% 4.37/4.57      (![X20 : $i, X21 : $i, X22 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ X22)
% 4.37/4.57           = (k4_xboole_0 @ X20 @ (k2_xboole_0 @ X21 @ X22)))),
% 4.37/4.57      inference('cnf', [status(esa)], [t41_xboole_1])).
% 4.37/4.57  thf('87', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 4.37/4.57      inference('demod', [status(thm)], ['34', '37'])).
% 4.37/4.57  thf('88', plain,
% 4.37/4.57      (![X15 : $i, X16 : $i]:
% 4.37/4.57         ((k2_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15))
% 4.37/4.57           = (k2_xboole_0 @ X15 @ X16))),
% 4.37/4.57      inference('cnf', [status(esa)], [t39_xboole_1])).
% 4.37/4.57  thf('89', plain,
% 4.37/4.57      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 4.37/4.57      inference('sup+', [status(thm)], ['87', '88'])).
% 4.37/4.57  thf('90', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 4.37/4.57      inference('demod', [status(thm)], ['19', '20'])).
% 4.37/4.57  thf('91', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 4.37/4.57      inference('demod', [status(thm)], ['89', '90'])).
% 4.37/4.57  thf('92', plain,
% 4.37/4.57      (![X20 : $i, X21 : $i, X22 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ X22)
% 4.37/4.57           = (k4_xboole_0 @ X20 @ (k2_xboole_0 @ X21 @ X22)))),
% 4.37/4.57      inference('cnf', [status(esa)], [t41_xboole_1])).
% 4.37/4.57  thf('93', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 4.37/4.57           = (k4_xboole_0 @ X1 @ X0))),
% 4.37/4.57      inference('sup+', [status(thm)], ['91', '92'])).
% 4.37/4.57  thf('94', plain,
% 4.37/4.57      (![X23 : $i, X24 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 4.37/4.57           = (k3_xboole_0 @ X23 @ X24))),
% 4.37/4.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.37/4.57  thf('95', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 4.37/4.57           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 4.37/4.57      inference('sup+', [status(thm)], ['93', '94'])).
% 4.37/4.57  thf('96', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 4.37/4.57      inference('demod', [status(thm)], ['34', '37'])).
% 4.37/4.57  thf('97', plain,
% 4.37/4.57      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 4.37/4.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.37/4.57  thf('98', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]:
% 4.37/4.57         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 4.37/4.57      inference('demod', [status(thm)], ['95', '96', '97'])).
% 4.37/4.57  thf('99', plain,
% 4.37/4.57      (![X4 : $i, X6 : $i]:
% 4.37/4.57         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 4.37/4.57      inference('cnf', [status(esa)], [d7_xboole_0])).
% 4.37/4.57  thf('100', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]:
% 4.37/4.57         (((k1_xboole_0) != (k1_xboole_0))
% 4.37/4.57          | (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 4.37/4.57      inference('sup-', [status(thm)], ['98', '99'])).
% 4.37/4.57  thf('101', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 4.37/4.57      inference('simplify', [status(thm)], ['100'])).
% 4.37/4.57  thf('102', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.37/4.57         (r1_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 4.37/4.57          (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 4.37/4.57      inference('sup+', [status(thm)], ['86', '101'])).
% 4.37/4.57  thf('103', plain,
% 4.37/4.57      ((![X0 : $i]:
% 4.37/4.57          (r1_xboole_0 @ (k2_xboole_0 @ sk_B @ X0) @ (k4_xboole_0 @ sk_A @ X0)))
% 4.37/4.57         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 4.37/4.57      inference('sup+', [status(thm)], ['85', '102'])).
% 4.37/4.57  thf('104', plain,
% 4.37/4.57      (((r1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ sk_A))
% 4.37/4.57         <= (((r1_xboole_0 @ sk_A @ sk_B)) & ((r1_xboole_0 @ sk_A @ sk_C_2)))),
% 4.37/4.57      inference('sup+', [status(thm)], ['65', '103'])).
% 4.37/4.57  thf(t4_xboole_0, axiom,
% 4.37/4.57    (![A:$i,B:$i]:
% 4.37/4.57     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 4.37/4.57            ( r1_xboole_0 @ A @ B ) ) ) & 
% 4.37/4.57       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 4.37/4.57            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 4.37/4.57  thf('105', plain,
% 4.37/4.57      (![X11 : $i, X12 : $i]:
% 4.37/4.57         ((r1_xboole_0 @ X11 @ X12)
% 4.37/4.57          | (r2_hidden @ (sk_C_1 @ X12 @ X11) @ (k3_xboole_0 @ X11 @ X12)))),
% 4.37/4.57      inference('cnf', [status(esa)], [t4_xboole_0])).
% 4.37/4.57  thf('106', plain,
% 4.37/4.57      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 4.37/4.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.37/4.57  thf('107', plain,
% 4.37/4.57      (![X11 : $i, X13 : $i, X14 : $i]:
% 4.37/4.57         (~ (r2_hidden @ X13 @ (k3_xboole_0 @ X11 @ X14))
% 4.37/4.57          | ~ (r1_xboole_0 @ X11 @ X14))),
% 4.37/4.57      inference('cnf', [status(esa)], [t4_xboole_0])).
% 4.37/4.57  thf('108', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.37/4.57         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 4.37/4.57          | ~ (r1_xboole_0 @ X0 @ X1))),
% 4.37/4.57      inference('sup-', [status(thm)], ['106', '107'])).
% 4.37/4.57  thf('109', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]:
% 4.37/4.57         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 4.37/4.57      inference('sup-', [status(thm)], ['105', '108'])).
% 4.37/4.57  thf('110', plain,
% 4.37/4.57      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2)))
% 4.37/4.57         <= (((r1_xboole_0 @ sk_A @ sk_B)) & ((r1_xboole_0 @ sk_A @ sk_C_2)))),
% 4.37/4.57      inference('sup-', [status(thm)], ['104', '109'])).
% 4.37/4.57  thf('111', plain,
% 4.37/4.57      ((~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2)))
% 4.37/4.57         <= (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))))),
% 4.37/4.57      inference('split', [status(esa)], ['0'])).
% 4.37/4.57  thf('112', plain,
% 4.37/4.57      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))) | 
% 4.37/4.57       ~ ((r1_xboole_0 @ sk_A @ sk_C_2)) | ~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 4.37/4.57      inference('sup-', [status(thm)], ['110', '111'])).
% 4.37/4.57  thf('113', plain,
% 4.37/4.57      ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))
% 4.37/4.57         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 4.37/4.57      inference('demod', [status(thm)], ['82', '83', '84'])).
% 4.37/4.57  thf('114', plain,
% 4.37/4.57      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2)))
% 4.37/4.57         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))))),
% 4.37/4.57      inference('split', [status(esa)], ['66'])).
% 4.37/4.57  thf('115', plain,
% 4.37/4.57      (![X4 : $i, X5 : $i]:
% 4.37/4.57         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 4.37/4.57      inference('cnf', [status(esa)], [d7_xboole_0])).
% 4.37/4.57  thf('116', plain,
% 4.37/4.57      ((((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2)) = (k1_xboole_0)))
% 4.37/4.57         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))))),
% 4.37/4.57      inference('sup-', [status(thm)], ['114', '115'])).
% 4.37/4.57  thf('117', plain,
% 4.37/4.57      (![X23 : $i, X24 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 4.37/4.57           = (k3_xboole_0 @ X23 @ X24))),
% 4.37/4.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.37/4.57  thf('118', plain,
% 4.37/4.57      (![X23 : $i, X24 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 4.37/4.57           = (k3_xboole_0 @ X23 @ X24))),
% 4.37/4.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.37/4.57  thf('119', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 4.37/4.57           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 4.37/4.57      inference('sup+', [status(thm)], ['117', '118'])).
% 4.37/4.57  thf('120', plain,
% 4.37/4.57      ((((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 4.37/4.57          = (k3_xboole_0 @ sk_A @ 
% 4.37/4.57             (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2)))))
% 4.37/4.57         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))))),
% 4.37/4.57      inference('sup+', [status(thm)], ['116', '119'])).
% 4.37/4.57  thf('121', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 4.37/4.57      inference('cnf', [status(esa)], [t3_boole])).
% 4.37/4.57  thf('122', plain,
% 4.37/4.57      (![X20 : $i, X21 : $i, X22 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ X22)
% 4.37/4.57           = (k4_xboole_0 @ X20 @ (k2_xboole_0 @ X21 @ X22)))),
% 4.37/4.57      inference('cnf', [status(esa)], [t41_xboole_1])).
% 4.37/4.57  thf('123', plain,
% 4.37/4.57      ((((sk_A)
% 4.37/4.57          = (k3_xboole_0 @ sk_A @ 
% 4.37/4.57             (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C_2))))
% 4.37/4.57         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))))),
% 4.37/4.57      inference('demod', [status(thm)], ['120', '121', '122'])).
% 4.37/4.57  thf('124', plain,
% 4.37/4.57      ((((sk_A) = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C_2))))
% 4.37/4.57         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))) & 
% 4.37/4.57             ((r1_xboole_0 @ sk_A @ sk_B)))),
% 4.37/4.57      inference('sup+', [status(thm)], ['113', '123'])).
% 4.37/4.57  thf('125', plain,
% 4.37/4.57      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 4.37/4.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.37/4.57  thf('126', plain,
% 4.37/4.57      (![X23 : $i, X24 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 4.37/4.57           = (k3_xboole_0 @ X23 @ X24))),
% 4.37/4.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.37/4.57  thf('127', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 4.37/4.57      inference('demod', [status(thm)], ['56', '57'])).
% 4.37/4.57  thf('128', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 4.37/4.57      inference('sup+', [status(thm)], ['126', '127'])).
% 4.37/4.57  thf('129', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 4.37/4.57      inference('sup+', [status(thm)], ['125', '128'])).
% 4.37/4.57  thf('130', plain,
% 4.37/4.57      ((((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C_2)) = (k1_xboole_0)))
% 4.37/4.57         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))) & 
% 4.37/4.57             ((r1_xboole_0 @ sk_A @ sk_B)))),
% 4.37/4.57      inference('sup+', [status(thm)], ['124', '129'])).
% 4.37/4.57  thf('131', plain,
% 4.37/4.57      (![X23 : $i, X24 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 4.37/4.57           = (k3_xboole_0 @ X23 @ X24))),
% 4.37/4.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.37/4.57  thf('132', plain,
% 4.37/4.57      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 4.37/4.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.37/4.57  thf('133', plain,
% 4.37/4.57      ((((k3_xboole_0 @ sk_C_2 @ sk_A) = (k1_xboole_0)))
% 4.37/4.57         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))) & 
% 4.37/4.57             ((r1_xboole_0 @ sk_A @ sk_B)))),
% 4.37/4.57      inference('demod', [status(thm)], ['130', '131', '132'])).
% 4.37/4.57  thf('134', plain,
% 4.37/4.57      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 4.37/4.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.37/4.57  thf('135', plain,
% 4.37/4.57      (![X4 : $i, X6 : $i]:
% 4.37/4.57         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 4.37/4.57      inference('cnf', [status(esa)], [d7_xboole_0])).
% 4.37/4.57  thf('136', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]:
% 4.37/4.57         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 4.37/4.57      inference('sup-', [status(thm)], ['134', '135'])).
% 4.37/4.57  thf('137', plain,
% 4.37/4.57      (((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_C_2)))
% 4.37/4.57         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))) & 
% 4.37/4.57             ((r1_xboole_0 @ sk_A @ sk_B)))),
% 4.37/4.57      inference('sup-', [status(thm)], ['133', '136'])).
% 4.37/4.57  thf('138', plain,
% 4.37/4.57      (((r1_xboole_0 @ sk_A @ sk_C_2))
% 4.37/4.57         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))) & 
% 4.37/4.57             ((r1_xboole_0 @ sk_A @ sk_B)))),
% 4.37/4.57      inference('simplify', [status(thm)], ['137'])).
% 4.37/4.57  thf('139', plain,
% 4.37/4.57      ((~ (r1_xboole_0 @ sk_A @ sk_C_2)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C_2)))),
% 4.37/4.57      inference('split', [status(esa)], ['0'])).
% 4.37/4.57  thf('140', plain,
% 4.37/4.57      (((r1_xboole_0 @ sk_A @ sk_C_2)) | 
% 4.37/4.57       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))) | 
% 4.37/4.57       ~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 4.37/4.57      inference('sup-', [status(thm)], ['138', '139'])).
% 4.37/4.57  thf('141', plain, (~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 4.37/4.57      inference('sat_resolution*', [status(thm)], ['3', '4', '112', '140'])).
% 4.37/4.57  thf('142', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 4.37/4.57      inference('simpl_trail', [status(thm)], ['1', '141'])).
% 4.37/4.57  thf('143', plain,
% 4.37/4.57      ((((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2)) = (k1_xboole_0)))
% 4.37/4.57         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))))),
% 4.37/4.57      inference('sup-', [status(thm)], ['114', '115'])).
% 4.37/4.57  thf('144', plain,
% 4.37/4.57      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))) | 
% 4.37/4.57       ((r1_xboole_0 @ sk_A @ sk_B))),
% 4.37/4.57      inference('split', [status(esa)], ['66'])).
% 4.37/4.57  thf('145', plain, (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 4.37/4.57      inference('sat_resolution*', [status(thm)],
% 4.37/4.57                ['3', '4', '112', '140', '144'])).
% 4.37/4.57  thf('146', plain,
% 4.37/4.57      (((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2)) = (k1_xboole_0))),
% 4.37/4.57      inference('simpl_trail', [status(thm)], ['143', '145'])).
% 4.37/4.57  thf('147', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 4.37/4.57           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 4.37/4.57      inference('sup+', [status(thm)], ['53', '54'])).
% 4.37/4.57  thf('148', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]:
% 4.37/4.57         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 4.37/4.57           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 4.37/4.57      inference('demod', [status(thm)], ['12', '13', '14'])).
% 4.37/4.57  thf('149', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.37/4.57         ((k2_xboole_0 @ (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1)) @ 
% 4.37/4.57           (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 4.37/4.57           = (k2_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1))))),
% 4.37/4.57      inference('sup+', [status(thm)], ['147', '148'])).
% 4.37/4.57  thf('150', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 4.37/4.57           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 4.37/4.57      inference('sup+', [status(thm)], ['53', '54'])).
% 4.37/4.57  thf('151', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.37/4.57         ((k2_xboole_0 @ (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1)) @ 
% 4.37/4.57           (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 4.37/4.57           = (k2_xboole_0 @ X2 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))),
% 4.37/4.57      inference('demod', [status(thm)], ['149', '150'])).
% 4.37/4.57  thf('152', plain,
% 4.37/4.57      (((k2_xboole_0 @ k1_xboole_0 @ 
% 4.37/4.57         (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C_2) @ sk_B))
% 4.37/4.57         = (k2_xboole_0 @ sk_A @ 
% 4.37/4.57            (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C_2) @ sk_B)))),
% 4.37/4.57      inference('sup+', [status(thm)], ['146', '151'])).
% 4.37/4.57  thf('153', plain,
% 4.37/4.57      ((((k4_xboole_0 @ sk_A @ sk_C_2) = (sk_A)))
% 4.37/4.57         <= (((r1_xboole_0 @ sk_A @ sk_C_2)))),
% 4.37/4.57      inference('demod', [status(thm)], ['62', '63', '64'])).
% 4.37/4.57  thf('154', plain,
% 4.37/4.57      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 4.37/4.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.37/4.57  thf('155', plain,
% 4.37/4.57      (![X11 : $i, X12 : $i]:
% 4.37/4.57         ((r1_xboole_0 @ X11 @ X12)
% 4.37/4.57          | (r2_hidden @ (sk_C_1 @ X12 @ X11) @ (k3_xboole_0 @ X11 @ X12)))),
% 4.37/4.57      inference('cnf', [status(esa)], [t4_xboole_0])).
% 4.37/4.57  thf('156', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]:
% 4.37/4.57         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 4.37/4.57          | (r1_xboole_0 @ X0 @ X1))),
% 4.37/4.57      inference('sup+', [status(thm)], ['154', '155'])).
% 4.37/4.57  thf('157', plain,
% 4.37/4.57      ((((sk_A)
% 4.37/4.57          = (k3_xboole_0 @ sk_A @ 
% 4.37/4.57             (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C_2))))
% 4.37/4.57         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))))),
% 4.37/4.57      inference('demod', [status(thm)], ['120', '121', '122'])).
% 4.37/4.57  thf('158', plain,
% 4.37/4.57      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 4.37/4.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.37/4.57  thf('159', plain,
% 4.37/4.57      (![X23 : $i, X24 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 4.37/4.57           = (k3_xboole_0 @ X23 @ X24))),
% 4.37/4.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.37/4.57  thf('160', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 4.37/4.57           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 4.37/4.57      inference('sup+', [status(thm)], ['53', '54'])).
% 4.37/4.57  thf('161', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]:
% 4.37/4.57         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 4.37/4.57      inference('demod', [status(thm)], ['95', '96', '97'])).
% 4.37/4.57  thf('162', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.37/4.57         ((k1_xboole_0)
% 4.37/4.57           = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ 
% 4.37/4.57              (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))),
% 4.37/4.57      inference('sup+', [status(thm)], ['160', '161'])).
% 4.37/4.57  thf('163', plain,
% 4.37/4.57      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 4.37/4.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.37/4.57  thf('164', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 4.37/4.57      inference('sup+', [status(thm)], ['126', '127'])).
% 4.37/4.57  thf('165', plain,
% 4.37/4.57      (![X15 : $i, X16 : $i]:
% 4.37/4.57         ((k2_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15))
% 4.37/4.57           = (k2_xboole_0 @ X15 @ X16))),
% 4.37/4.57      inference('cnf', [status(esa)], [t39_xboole_1])).
% 4.37/4.57  thf('166', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]:
% 4.37/4.57         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 4.37/4.57           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 4.37/4.57      inference('sup+', [status(thm)], ['164', '165'])).
% 4.37/4.57  thf('167', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 4.37/4.57      inference('demod', [status(thm)], ['19', '20'])).
% 4.37/4.57  thf('168', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]:
% 4.37/4.57         ((X1) = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 4.37/4.57      inference('demod', [status(thm)], ['166', '167'])).
% 4.37/4.57  thf('169', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 4.37/4.57      inference('demod', [status(thm)], ['34', '37'])).
% 4.37/4.57  thf('170', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 4.37/4.57           = (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 4.37/4.57      inference('sup+', [status(thm)], ['39', '40'])).
% 4.37/4.57  thf('171', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 4.37/4.57           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 4.37/4.57      inference('sup+', [status(thm)], ['169', '170'])).
% 4.37/4.57  thf('172', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 4.37/4.57      inference('cnf', [status(esa)], [t3_boole])).
% 4.37/4.57  thf('173', plain,
% 4.37/4.57      (![X15 : $i, X16 : $i]:
% 4.37/4.57         ((k2_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15))
% 4.37/4.57           = (k2_xboole_0 @ X15 @ X16))),
% 4.37/4.57      inference('cnf', [status(esa)], [t39_xboole_1])).
% 4.37/4.57  thf('174', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]:
% 4.37/4.57         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 4.37/4.57      inference('demod', [status(thm)], ['171', '172', '173'])).
% 4.37/4.57  thf('175', plain,
% 4.37/4.57      (![X11 : $i, X13 : $i, X14 : $i]:
% 4.37/4.57         (~ (r2_hidden @ X13 @ (k3_xboole_0 @ X11 @ X14))
% 4.37/4.57          | ~ (r1_xboole_0 @ X11 @ X14))),
% 4.37/4.57      inference('cnf', [status(esa)], [t4_xboole_0])).
% 4.37/4.57  thf('176', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.37/4.57         (~ (r2_hidden @ X2 @ X0)
% 4.37/4.57          | ~ (r1_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 4.37/4.57      inference('sup-', [status(thm)], ['174', '175'])).
% 4.37/4.57  thf('177', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.37/4.57         (~ (r1_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 4.37/4.57          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 4.37/4.57      inference('sup-', [status(thm)], ['168', '176'])).
% 4.37/4.57  thf('178', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.37/4.57         (~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 4.37/4.57          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 4.37/4.57      inference('sup-', [status(thm)], ['163', '177'])).
% 4.37/4.57  thf('179', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.37/4.57         (~ (r1_xboole_0 @ k1_xboole_0 @ 
% 4.37/4.57             (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 4.37/4.57          | ~ (r2_hidden @ X3 @ 
% 4.37/4.57               (k3_xboole_0 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) @ 
% 4.37/4.57                (k2_xboole_0 @ X0 @ X1))))),
% 4.37/4.57      inference('sup-', [status(thm)], ['162', '178'])).
% 4.37/4.57  thf('180', plain,
% 4.37/4.57      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 4.37/4.57      inference('sup-', [status(thm)], ['35', '36'])).
% 4.37/4.57  thf('181', plain,
% 4.37/4.57      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 4.37/4.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.37/4.57  thf('182', plain,
% 4.37/4.57      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 4.37/4.57      inference('sup+', [status(thm)], ['180', '181'])).
% 4.37/4.57  thf('183', plain,
% 4.37/4.57      (![X4 : $i, X6 : $i]:
% 4.37/4.57         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 4.37/4.57      inference('cnf', [status(esa)], [d7_xboole_0])).
% 4.37/4.57  thf('184', plain,
% 4.37/4.57      (![X0 : $i]:
% 4.37/4.57         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 4.37/4.57      inference('sup-', [status(thm)], ['182', '183'])).
% 4.37/4.57  thf('185', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 4.37/4.57      inference('simplify', [status(thm)], ['184'])).
% 4.37/4.57  thf('186', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 4.37/4.57           = (k4_xboole_0 @ X1 @ X0))),
% 4.37/4.57      inference('sup+', [status(thm)], ['91', '92'])).
% 4.37/4.57  thf('187', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 4.37/4.57           = (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 4.37/4.57      inference('sup+', [status(thm)], ['39', '40'])).
% 4.37/4.57  thf('188', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 4.37/4.57           (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))
% 4.37/4.57           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 4.37/4.57      inference('sup+', [status(thm)], ['186', '187'])).
% 4.37/4.57  thf('189', plain,
% 4.37/4.57      (![X23 : $i, X24 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 4.37/4.57           = (k3_xboole_0 @ X23 @ X24))),
% 4.37/4.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.37/4.57  thf('190', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.37/4.57         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 4.37/4.57           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 4.37/4.57      inference('demod', [status(thm)], ['188', '189'])).
% 4.37/4.57  thf('191', plain,
% 4.37/4.57      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 4.37/4.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.37/4.57  thf('192', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.37/4.57         ~ (r2_hidden @ X3 @ 
% 4.37/4.57            (k3_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))),
% 4.37/4.57      inference('demod', [status(thm)], ['179', '185', '190', '191'])).
% 4.37/4.57  thf('193', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.37/4.57         ~ (r2_hidden @ X3 @ 
% 4.37/4.57            (k3_xboole_0 @ X1 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))),
% 4.37/4.57      inference('sup-', [status(thm)], ['159', '192'])).
% 4.37/4.57  thf('194', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.37/4.57         ~ (r2_hidden @ X3 @ 
% 4.37/4.57            (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 4.37/4.57      inference('sup-', [status(thm)], ['158', '193'])).
% 4.37/4.57  thf('195', plain,
% 4.37/4.57      ((![X0 : $i]: ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_C_2 @ sk_A)))
% 4.37/4.57         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))))),
% 4.37/4.57      inference('sup-', [status(thm)], ['157', '194'])).
% 4.37/4.57  thf('196', plain,
% 4.37/4.57      (((r1_xboole_0 @ sk_A @ sk_C_2))
% 4.37/4.57         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))))),
% 4.37/4.57      inference('sup-', [status(thm)], ['156', '195'])).
% 4.37/4.57  thf('197', plain,
% 4.37/4.57      ((~ (r1_xboole_0 @ sk_A @ sk_C_2)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C_2)))),
% 4.37/4.57      inference('split', [status(esa)], ['0'])).
% 4.37/4.57  thf('198', plain,
% 4.37/4.57      (((r1_xboole_0 @ sk_A @ sk_C_2)) | 
% 4.37/4.57       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 4.37/4.57      inference('sup-', [status(thm)], ['196', '197'])).
% 4.37/4.57  thf('199', plain, (((r1_xboole_0 @ sk_A @ sk_C_2))),
% 4.37/4.57      inference('sat_resolution*', [status(thm)],
% 4.37/4.57                ['3', '4', '112', '140', '144', '198'])).
% 4.37/4.57  thf('200', plain, (((k4_xboole_0 @ sk_A @ sk_C_2) = (sk_A))),
% 4.37/4.57      inference('simpl_trail', [status(thm)], ['153', '199'])).
% 4.37/4.57  thf('201', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 4.37/4.57      inference('sup+', [status(thm)], ['21', '22'])).
% 4.37/4.57  thf('202', plain, (((k4_xboole_0 @ sk_A @ sk_C_2) = (sk_A))),
% 4.37/4.57      inference('simpl_trail', [status(thm)], ['153', '199'])).
% 4.37/4.57  thf('203', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]:
% 4.37/4.57         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 4.37/4.57      inference('demod', [status(thm)], ['56', '57'])).
% 4.37/4.57  thf('204', plain,
% 4.37/4.57      (![X15 : $i, X16 : $i]:
% 4.37/4.57         ((k2_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15))
% 4.37/4.57           = (k2_xboole_0 @ X15 @ X16))),
% 4.37/4.57      inference('cnf', [status(esa)], [t39_xboole_1])).
% 4.37/4.57  thf('205', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]:
% 4.37/4.57         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 4.37/4.57           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 4.37/4.57      inference('sup+', [status(thm)], ['203', '204'])).
% 4.37/4.57  thf('206', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 4.37/4.57      inference('demod', [status(thm)], ['19', '20'])).
% 4.37/4.57  thf('207', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]:
% 4.37/4.57         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 4.37/4.57      inference('demod', [status(thm)], ['205', '206'])).
% 4.37/4.57  thf('208', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 4.37/4.57      inference('demod', [status(thm)], ['152', '200', '201', '202', '207'])).
% 4.37/4.57  thf('209', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]:
% 4.37/4.57         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 4.37/4.57      inference('demod', [status(thm)], ['95', '96', '97'])).
% 4.37/4.57  thf('210', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]:
% 4.37/4.57         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 4.37/4.57      inference('sup-', [status(thm)], ['134', '135'])).
% 4.37/4.57  thf('211', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]:
% 4.37/4.57         (((k1_xboole_0) != (k1_xboole_0))
% 4.37/4.57          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 4.37/4.57      inference('sup-', [status(thm)], ['209', '210'])).
% 4.37/4.57  thf('212', plain,
% 4.37/4.57      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 4.37/4.57      inference('simplify', [status(thm)], ['211'])).
% 4.37/4.57  thf('213', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 4.37/4.57      inference('sup+', [status(thm)], ['208', '212'])).
% 4.37/4.57  thf('214', plain, ($false), inference('demod', [status(thm)], ['142', '213'])).
% 4.37/4.57  
% 4.37/4.57  % SZS output end Refutation
% 4.37/4.57  
% 4.43/4.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
