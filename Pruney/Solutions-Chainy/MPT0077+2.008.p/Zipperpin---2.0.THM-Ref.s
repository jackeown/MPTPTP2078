%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IKtlNsad1U

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:50 EST 2020

% Result     : Theorem 40.71s
% Output     : Refutation 40.71s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 894 expanded)
%              Number of leaves         :   20 ( 268 expanded)
%              Depth                    :   31
%              Number of atoms          : 1515 (8279 expanded)
%              Number of equality atoms :   83 ( 445 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C_1 )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
   <= ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C_1 )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('5',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k4_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

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

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C @ X14 @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('11',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('13',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('19',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C @ X14 @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('23',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('26',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('30',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['21','31'])).

thf('33',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('36',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('43',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['34','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['9','20','44'])).

thf('46',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C @ X14 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('47',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('48',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X2 ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X1 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['45','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['14'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C @ X14 @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('54',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X13 )
      | ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_xboole_0 @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ X1 )
      | ~ ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X2 @ X1 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['4','57'])).

thf('59',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_B )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('60',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['9','20','44'])).

thf('64',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C @ X14 @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('65',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['63','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['14'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C @ X14 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('71',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X13 )
      | ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_xboole_0 @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ~ ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['62','74'])).

thf('76',plain,
    ( ( r1_xboole_0 @ sk_C_1 @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['61','75'])).

thf('77',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('78',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C_1 )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C_1 )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('80',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C_1 )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','60','80'])).

thf('82',plain,(
    ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(simpl_trail,[status(thm)],['1','81'])).

thf('83',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
    | ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C_1 )
   <= ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['83'])).

thf('85',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('86',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C_1 )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['83'])).

thf('88',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['2','60','80','87'])).

thf('89',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['86','88'])).

thf('90',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('91',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k4_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('92',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['93','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) @ X0 )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['14'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,
    ( ( r1_xboole_0 @ ( k2_xboole_0 @ sk_B @ k1_xboole_0 ) @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['90','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('107',plain,
    ( ( r1_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ sk_B ) @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C @ X14 @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('109',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ ( k2_xboole_0 @ k1_xboole_0 @ sk_B ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['107','113'])).

thf('115',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('116',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['2','60','80','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ ( k2_xboole_0 @ k1_xboole_0 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['114','116'])).

thf('118',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['118'])).

thf('120',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['118'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['118'])).

thf('126',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X13 )
      | ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_xboole_0 @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('127',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['124','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ ( k2_xboole_0 @ k1_xboole_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['117','129'])).

thf('131',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k4_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('133',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k4_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('134',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k4_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('136',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k4_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('138',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k4_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('139',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k2_xboole_0 @ X0 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k4_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('141',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k4_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('142',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X3 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X3 ) ) ) ) ),
    inference(demod,[status(thm)],['139','140','141'])).

thf('143',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['136','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['130','131','143'])).

thf('145',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ( ( k3_xboole_0 @ X8 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_A @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['89','150'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('153',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,(
    r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,(
    $false ),
    inference(demod,[status(thm)],['82','154'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IKtlNsad1U
% 0.13/0.37  % Computer   : n011.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 19:46:27 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 40.71/40.90  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 40.71/40.90  % Solved by: fo/fo7.sh
% 40.71/40.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 40.71/40.90  % done 21700 iterations in 40.414s
% 40.71/40.90  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 40.71/40.90  % SZS output start Refutation
% 40.71/40.90  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 40.71/40.90  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 40.71/40.90  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 40.71/40.90  thf(sk_C_1_type, type, sk_C_1: $i).
% 40.71/40.90  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 40.71/40.90  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 40.71/40.90  thf(sk_A_type, type, sk_A: $i).
% 40.71/40.90  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 40.71/40.90  thf(sk_B_type, type, sk_B: $i).
% 40.71/40.90  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 40.71/40.90  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 40.71/40.90  thf(t70_xboole_1, conjecture,
% 40.71/40.90    (![A:$i,B:$i,C:$i]:
% 40.71/40.90     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 40.71/40.90            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 40.71/40.90       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 40.71/40.90            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 40.71/40.90  thf(zf_stmt_0, negated_conjecture,
% 40.71/40.90    (~( ![A:$i,B:$i,C:$i]:
% 40.71/40.90        ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 40.71/40.90               ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 40.71/40.90          ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 40.71/40.90               ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ) )),
% 40.71/40.90    inference('cnf.neg', [status(esa)], [t70_xboole_1])).
% 40.71/40.90  thf('0', plain,
% 40.71/40.90      ((~ (r1_xboole_0 @ sk_A @ sk_C_1)
% 40.71/40.90        | ~ (r1_xboole_0 @ sk_A @ sk_B)
% 40.71/40.90        | ~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 40.71/40.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 40.71/40.90  thf('1', plain,
% 40.71/40.90      ((~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))
% 40.71/40.90         <= (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))))),
% 40.71/40.90      inference('split', [status(esa)], ['0'])).
% 40.71/40.90  thf('2', plain,
% 40.71/40.90      (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))) | 
% 40.71/40.90       ~ ((r1_xboole_0 @ sk_A @ sk_C_1)) | ~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 40.71/40.90      inference('split', [status(esa)], ['0'])).
% 40.71/40.90  thf('3', plain,
% 40.71/40.90      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))
% 40.71/40.90        | (r1_xboole_0 @ sk_A @ sk_B))),
% 40.71/40.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 40.71/40.90  thf('4', plain,
% 40.71/40.90      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))
% 40.71/40.90         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))))),
% 40.71/40.90      inference('split', [status(esa)], ['3'])).
% 40.71/40.90  thf(t3_boole, axiom,
% 40.71/40.90    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 40.71/40.90  thf('5', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 40.71/40.90      inference('cnf', [status(esa)], [t3_boole])).
% 40.71/40.90  thf(t48_xboole_1, axiom,
% 40.71/40.90    (![A:$i,B:$i]:
% 40.71/40.90     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 40.71/40.90  thf('6', plain,
% 40.71/40.90      (![X21 : $i, X22 : $i]:
% 40.71/40.90         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 40.71/40.90           = (k3_xboole_0 @ X21 @ X22))),
% 40.71/40.90      inference('cnf', [status(esa)], [t48_xboole_1])).
% 40.71/40.90  thf(t41_xboole_1, axiom,
% 40.71/40.90    (![A:$i,B:$i,C:$i]:
% 40.71/40.90     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 40.71/40.90       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 40.71/40.90  thf('7', plain,
% 40.71/40.90      (![X18 : $i, X19 : $i, X20 : $i]:
% 40.71/40.90         ((k4_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X20)
% 40.71/40.90           = (k4_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20)))),
% 40.71/40.90      inference('cnf', [status(esa)], [t41_xboole_1])).
% 40.71/40.90  thf('8', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.71/40.90         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 40.71/40.90           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 40.71/40.90      inference('sup+', [status(thm)], ['6', '7'])).
% 40.71/40.90  thf('9', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i]:
% 40.71/40.90         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X1)
% 40.71/40.90           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 40.71/40.90      inference('sup+', [status(thm)], ['5', '8'])).
% 40.71/40.90  thf(t3_xboole_0, axiom,
% 40.71/40.90    (![A:$i,B:$i]:
% 40.71/40.90     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 40.71/40.90            ( r1_xboole_0 @ A @ B ) ) ) & 
% 40.71/40.90       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 40.71/40.90            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 40.71/40.90  thf('10', plain,
% 40.71/40.90      (![X13 : $i, X14 : $i]:
% 40.71/40.90         ((r1_xboole_0 @ X13 @ X14) | (r2_hidden @ (sk_C @ X14 @ X13) @ X13))),
% 40.71/40.90      inference('cnf', [status(esa)], [t3_xboole_0])).
% 40.71/40.90  thf('11', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 40.71/40.90      inference('cnf', [status(esa)], [t3_boole])).
% 40.71/40.90  thf(d5_xboole_0, axiom,
% 40.71/40.90    (![A:$i,B:$i,C:$i]:
% 40.71/40.90     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 40.71/40.90       ( ![D:$i]:
% 40.71/40.90         ( ( r2_hidden @ D @ C ) <=>
% 40.71/40.90           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 40.71/40.90  thf('12', plain,
% 40.71/40.90      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 40.71/40.90         (~ (r2_hidden @ X6 @ X5)
% 40.71/40.90          | ~ (r2_hidden @ X6 @ X4)
% 40.71/40.90          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 40.71/40.90      inference('cnf', [status(esa)], [d5_xboole_0])).
% 40.71/40.90  thf('13', plain,
% 40.71/40.90      (![X3 : $i, X4 : $i, X6 : $i]:
% 40.71/40.90         (~ (r2_hidden @ X6 @ X4)
% 40.71/40.90          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 40.71/40.90      inference('simplify', [status(thm)], ['12'])).
% 40.71/40.90  thf('14', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i]:
% 40.71/40.90         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 40.71/40.90      inference('sup-', [status(thm)], ['11', '13'])).
% 40.71/40.90  thf('15', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 40.71/40.90      inference('condensation', [status(thm)], ['14'])).
% 40.71/40.90  thf('16', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 40.71/40.90      inference('sup-', [status(thm)], ['10', '15'])).
% 40.71/40.90  thf(symmetry_r1_xboole_0, axiom,
% 40.71/40.90    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 40.71/40.90  thf('17', plain,
% 40.71/40.90      (![X11 : $i, X12 : $i]:
% 40.71/40.90         ((r1_xboole_0 @ X11 @ X12) | ~ (r1_xboole_0 @ X12 @ X11))),
% 40.71/40.90      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 40.71/40.90  thf('18', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 40.71/40.90      inference('sup-', [status(thm)], ['16', '17'])).
% 40.71/40.90  thf(d7_xboole_0, axiom,
% 40.71/40.90    (![A:$i,B:$i]:
% 40.71/40.90     ( ( r1_xboole_0 @ A @ B ) <=>
% 40.71/40.90       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 40.71/40.90  thf('19', plain,
% 40.71/40.90      (![X8 : $i, X9 : $i]:
% 40.71/40.90         (((k3_xboole_0 @ X8 @ X9) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 40.71/40.90      inference('cnf', [status(esa)], [d7_xboole_0])).
% 40.71/40.90  thf('20', plain,
% 40.71/40.90      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 40.71/40.90      inference('sup-', [status(thm)], ['18', '19'])).
% 40.71/40.90  thf('21', plain,
% 40.71/40.90      (![X13 : $i, X14 : $i]:
% 40.71/40.90         ((r1_xboole_0 @ X13 @ X14) | (r2_hidden @ (sk_C @ X14 @ X13) @ X13))),
% 40.71/40.90      inference('cnf', [status(esa)], [t3_xboole_0])).
% 40.71/40.90  thf('22', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 40.71/40.90      inference('sup-', [status(thm)], ['10', '15'])).
% 40.71/40.90  thf('23', plain,
% 40.71/40.90      (![X8 : $i, X9 : $i]:
% 40.71/40.90         (((k3_xboole_0 @ X8 @ X9) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 40.71/40.90      inference('cnf', [status(esa)], [d7_xboole_0])).
% 40.71/40.90  thf('24', plain,
% 40.71/40.90      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 40.71/40.90      inference('sup-', [status(thm)], ['22', '23'])).
% 40.71/40.90  thf('25', plain,
% 40.71/40.90      (![X21 : $i, X22 : $i]:
% 40.71/40.90         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 40.71/40.90           = (k3_xboole_0 @ X21 @ X22))),
% 40.71/40.90      inference('cnf', [status(esa)], [t48_xboole_1])).
% 40.71/40.90  thf('26', plain,
% 40.71/40.90      (![X3 : $i, X4 : $i, X6 : $i]:
% 40.71/40.90         (~ (r2_hidden @ X6 @ X4)
% 40.71/40.90          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 40.71/40.90      inference('simplify', [status(thm)], ['12'])).
% 40.71/40.90  thf('27', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.71/40.90         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 40.71/40.90          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 40.71/40.90      inference('sup-', [status(thm)], ['25', '26'])).
% 40.71/40.90  thf('28', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i]:
% 40.71/40.90         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 40.71/40.90          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 40.71/40.90      inference('sup-', [status(thm)], ['24', '27'])).
% 40.71/40.90  thf('29', plain,
% 40.71/40.90      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 40.71/40.90         (~ (r2_hidden @ X6 @ X5)
% 40.71/40.90          | (r2_hidden @ X6 @ X3)
% 40.71/40.90          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 40.71/40.90      inference('cnf', [status(esa)], [d5_xboole_0])).
% 40.71/40.90  thf('30', plain,
% 40.71/40.90      (![X3 : $i, X4 : $i, X6 : $i]:
% 40.71/40.90         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 40.71/40.90      inference('simplify', [status(thm)], ['29'])).
% 40.71/40.90  thf('31', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i]:
% 40.71/40.90         ~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 40.71/40.90      inference('clc', [status(thm)], ['28', '30'])).
% 40.71/40.90  thf('32', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i]:
% 40.71/40.90         (r1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0) @ X1)),
% 40.71/40.90      inference('sup-', [status(thm)], ['21', '31'])).
% 40.71/40.90  thf('33', plain,
% 40.71/40.90      (![X8 : $i, X9 : $i]:
% 40.71/40.90         (((k3_xboole_0 @ X8 @ X9) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 40.71/40.90      inference('cnf', [status(esa)], [d7_xboole_0])).
% 40.71/40.90  thf('34', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i]:
% 40.71/40.90         ((k3_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X1) @ X0) = (k1_xboole_0))),
% 40.71/40.90      inference('sup-', [status(thm)], ['32', '33'])).
% 40.71/40.90  thf('35', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 40.71/40.90      inference('cnf', [status(esa)], [t3_boole])).
% 40.71/40.90  thf('36', plain,
% 40.71/40.90      (![X21 : $i, X22 : $i]:
% 40.71/40.90         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 40.71/40.90           = (k3_xboole_0 @ X21 @ X22))),
% 40.71/40.90      inference('cnf', [status(esa)], [t48_xboole_1])).
% 40.71/40.90  thf('37', plain,
% 40.71/40.90      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 40.71/40.90      inference('sup+', [status(thm)], ['35', '36'])).
% 40.71/40.90  thf('38', plain,
% 40.71/40.90      (![X21 : $i, X22 : $i]:
% 40.71/40.90         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 40.71/40.90           = (k3_xboole_0 @ X21 @ X22))),
% 40.71/40.90      inference('cnf', [status(esa)], [t48_xboole_1])).
% 40.71/40.90  thf('39', plain,
% 40.71/40.90      (![X0 : $i]:
% 40.71/40.90         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0))
% 40.71/40.90           = (k3_xboole_0 @ X0 @ X0))),
% 40.71/40.90      inference('sup+', [status(thm)], ['37', '38'])).
% 40.71/40.90  thf('40', plain,
% 40.71/40.90      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 40.71/40.90      inference('sup-', [status(thm)], ['18', '19'])).
% 40.71/40.90  thf('41', plain,
% 40.71/40.90      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 40.71/40.90      inference('demod', [status(thm)], ['39', '40'])).
% 40.71/40.90  thf('42', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 40.71/40.90      inference('cnf', [status(esa)], [t3_boole])).
% 40.71/40.90  thf('43', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 40.71/40.90      inference('demod', [status(thm)], ['41', '42'])).
% 40.71/40.90  thf('44', plain,
% 40.71/40.90      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 40.71/40.90      inference('sup+', [status(thm)], ['34', '43'])).
% 40.71/40.90  thf('45', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i]:
% 40.71/40.90         ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 40.71/40.90      inference('demod', [status(thm)], ['9', '20', '44'])).
% 40.71/40.90  thf('46', plain,
% 40.71/40.90      (![X13 : $i, X14 : $i]:
% 40.71/40.90         ((r1_xboole_0 @ X13 @ X14) | (r2_hidden @ (sk_C @ X14 @ X13) @ X14))),
% 40.71/40.90      inference('cnf', [status(esa)], [t3_xboole_0])).
% 40.71/40.90  thf('47', plain,
% 40.71/40.90      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 40.71/40.90         (~ (r2_hidden @ X2 @ X3)
% 40.71/40.90          | (r2_hidden @ X2 @ X4)
% 40.71/40.90          | (r2_hidden @ X2 @ X5)
% 40.71/40.90          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 40.71/40.90      inference('cnf', [status(esa)], [d5_xboole_0])).
% 40.71/40.90  thf('48', plain,
% 40.71/40.90      (![X2 : $i, X3 : $i, X4 : $i]:
% 40.71/40.90         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 40.71/40.90          | (r2_hidden @ X2 @ X4)
% 40.71/40.90          | ~ (r2_hidden @ X2 @ X3))),
% 40.71/40.90      inference('simplify', [status(thm)], ['47'])).
% 40.71/40.90  thf('49', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.71/40.90         ((r1_xboole_0 @ X1 @ X0)
% 40.71/40.90          | (r2_hidden @ (sk_C @ X0 @ X1) @ X2)
% 40.71/40.90          | (r2_hidden @ (sk_C @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X2)))),
% 40.71/40.90      inference('sup-', [status(thm)], ['46', '48'])).
% 40.71/40.90  thf('50', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.71/40.90         ((r2_hidden @ (sk_C @ X1 @ X2) @ k1_xboole_0)
% 40.71/40.90          | (r2_hidden @ (sk_C @ X1 @ X2) @ (k2_xboole_0 @ X1 @ X0))
% 40.71/40.90          | (r1_xboole_0 @ X2 @ X1))),
% 40.71/40.90      inference('sup+', [status(thm)], ['45', '49'])).
% 40.71/40.90  thf('51', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 40.71/40.90      inference('condensation', [status(thm)], ['14'])).
% 40.71/40.90  thf('52', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.71/40.90         ((r1_xboole_0 @ X2 @ X1)
% 40.71/40.90          | (r2_hidden @ (sk_C @ X1 @ X2) @ (k2_xboole_0 @ X1 @ X0)))),
% 40.71/40.90      inference('clc', [status(thm)], ['50', '51'])).
% 40.71/40.90  thf('53', plain,
% 40.71/40.90      (![X13 : $i, X14 : $i]:
% 40.71/40.90         ((r1_xboole_0 @ X13 @ X14) | (r2_hidden @ (sk_C @ X14 @ X13) @ X13))),
% 40.71/40.90      inference('cnf', [status(esa)], [t3_xboole_0])).
% 40.71/40.90  thf('54', plain,
% 40.71/40.90      (![X13 : $i, X15 : $i, X16 : $i]:
% 40.71/40.90         (~ (r2_hidden @ X15 @ X13)
% 40.71/40.90          | ~ (r2_hidden @ X15 @ X16)
% 40.71/40.90          | ~ (r1_xboole_0 @ X13 @ X16))),
% 40.71/40.90      inference('cnf', [status(esa)], [t3_xboole_0])).
% 40.71/40.90  thf('55', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.71/40.90         ((r1_xboole_0 @ X0 @ X1)
% 40.71/40.90          | ~ (r1_xboole_0 @ X0 @ X2)
% 40.71/40.90          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 40.71/40.90      inference('sup-', [status(thm)], ['53', '54'])).
% 40.71/40.90  thf('56', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.71/40.90         ((r1_xboole_0 @ X2 @ X1)
% 40.71/40.90          | ~ (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 40.71/40.90          | (r1_xboole_0 @ X2 @ X1))),
% 40.71/40.90      inference('sup-', [status(thm)], ['52', '55'])).
% 40.71/40.90  thf('57', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.71/40.90         (~ (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 40.71/40.90          | (r1_xboole_0 @ X2 @ X1))),
% 40.71/40.90      inference('simplify', [status(thm)], ['56'])).
% 40.71/40.90  thf('58', plain,
% 40.71/40.90      (((r1_xboole_0 @ sk_A @ sk_B))
% 40.71/40.90         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))))),
% 40.71/40.90      inference('sup-', [status(thm)], ['4', '57'])).
% 40.71/40.90  thf('59', plain,
% 40.71/40.90      ((~ (r1_xboole_0 @ sk_A @ sk_B)) <= (~ ((r1_xboole_0 @ sk_A @ sk_B)))),
% 40.71/40.90      inference('split', [status(esa)], ['0'])).
% 40.71/40.90  thf('60', plain,
% 40.71/40.90      (((r1_xboole_0 @ sk_A @ sk_B)) | 
% 40.71/40.90       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 40.71/40.90      inference('sup-', [status(thm)], ['58', '59'])).
% 40.71/40.90  thf('61', plain,
% 40.71/40.90      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))
% 40.71/40.90         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))))),
% 40.71/40.90      inference('split', [status(esa)], ['3'])).
% 40.71/40.90  thf(commutativity_k2_xboole_0, axiom,
% 40.71/40.90    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 40.71/40.90  thf('62', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 40.71/40.90      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 40.71/40.90  thf('63', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i]:
% 40.71/40.90         ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 40.71/40.90      inference('demod', [status(thm)], ['9', '20', '44'])).
% 40.71/40.90  thf('64', plain,
% 40.71/40.90      (![X13 : $i, X14 : $i]:
% 40.71/40.90         ((r1_xboole_0 @ X13 @ X14) | (r2_hidden @ (sk_C @ X14 @ X13) @ X13))),
% 40.71/40.90      inference('cnf', [status(esa)], [t3_xboole_0])).
% 40.71/40.90  thf('65', plain,
% 40.71/40.90      (![X2 : $i, X3 : $i, X4 : $i]:
% 40.71/40.90         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 40.71/40.90          | (r2_hidden @ X2 @ X4)
% 40.71/40.90          | ~ (r2_hidden @ X2 @ X3))),
% 40.71/40.90      inference('simplify', [status(thm)], ['47'])).
% 40.71/40.90  thf('66', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.71/40.90         ((r1_xboole_0 @ X0 @ X1)
% 40.71/40.90          | (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 40.71/40.90          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X2)))),
% 40.71/40.90      inference('sup-', [status(thm)], ['64', '65'])).
% 40.71/40.90  thf('67', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.71/40.90         ((r2_hidden @ (sk_C @ X2 @ X1) @ k1_xboole_0)
% 40.71/40.90          | (r2_hidden @ (sk_C @ X2 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 40.71/40.90          | (r1_xboole_0 @ X1 @ X2))),
% 40.71/40.90      inference('sup+', [status(thm)], ['63', '66'])).
% 40.71/40.90  thf('68', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 40.71/40.90      inference('condensation', [status(thm)], ['14'])).
% 40.71/40.90  thf('69', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.71/40.90         ((r1_xboole_0 @ X1 @ X2)
% 40.71/40.90          | (r2_hidden @ (sk_C @ X2 @ X1) @ (k2_xboole_0 @ X1 @ X0)))),
% 40.71/40.90      inference('clc', [status(thm)], ['67', '68'])).
% 40.71/40.90  thf('70', plain,
% 40.71/40.90      (![X13 : $i, X14 : $i]:
% 40.71/40.90         ((r1_xboole_0 @ X13 @ X14) | (r2_hidden @ (sk_C @ X14 @ X13) @ X14))),
% 40.71/40.90      inference('cnf', [status(esa)], [t3_xboole_0])).
% 40.71/40.90  thf('71', plain,
% 40.71/40.90      (![X13 : $i, X15 : $i, X16 : $i]:
% 40.71/40.90         (~ (r2_hidden @ X15 @ X13)
% 40.71/40.90          | ~ (r2_hidden @ X15 @ X16)
% 40.71/40.90          | ~ (r1_xboole_0 @ X13 @ X16))),
% 40.71/40.90      inference('cnf', [status(esa)], [t3_xboole_0])).
% 40.71/40.90  thf('72', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.71/40.90         ((r1_xboole_0 @ X1 @ X0)
% 40.71/40.90          | ~ (r1_xboole_0 @ X0 @ X2)
% 40.71/40.90          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 40.71/40.90      inference('sup-', [status(thm)], ['70', '71'])).
% 40.71/40.90  thf('73', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.71/40.90         ((r1_xboole_0 @ X1 @ X2)
% 40.71/40.90          | ~ (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 40.71/40.90          | (r1_xboole_0 @ X1 @ X2))),
% 40.71/40.90      inference('sup-', [status(thm)], ['69', '72'])).
% 40.71/40.90  thf('74', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.71/40.90         (~ (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 40.71/40.90          | (r1_xboole_0 @ X1 @ X2))),
% 40.71/40.90      inference('simplify', [status(thm)], ['73'])).
% 40.71/40.90  thf('75', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.71/40.90         (~ (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 40.71/40.90          | (r1_xboole_0 @ X0 @ X2))),
% 40.71/40.90      inference('sup-', [status(thm)], ['62', '74'])).
% 40.71/40.90  thf('76', plain,
% 40.71/40.90      (((r1_xboole_0 @ sk_C_1 @ sk_A))
% 40.71/40.90         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))))),
% 40.71/40.90      inference('sup-', [status(thm)], ['61', '75'])).
% 40.71/40.90  thf('77', plain,
% 40.71/40.90      (![X11 : $i, X12 : $i]:
% 40.71/40.90         ((r1_xboole_0 @ X11 @ X12) | ~ (r1_xboole_0 @ X12 @ X11))),
% 40.71/40.90      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 40.71/40.90  thf('78', plain,
% 40.71/40.90      (((r1_xboole_0 @ sk_A @ sk_C_1))
% 40.71/40.90         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))))),
% 40.71/40.90      inference('sup-', [status(thm)], ['76', '77'])).
% 40.71/40.90  thf('79', plain,
% 40.71/40.90      ((~ (r1_xboole_0 @ sk_A @ sk_C_1)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 40.71/40.90      inference('split', [status(esa)], ['0'])).
% 40.71/40.90  thf('80', plain,
% 40.71/40.90      (((r1_xboole_0 @ sk_A @ sk_C_1)) | 
% 40.71/40.90       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 40.71/40.90      inference('sup-', [status(thm)], ['78', '79'])).
% 40.71/40.90  thf('81', plain, (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 40.71/40.90      inference('sat_resolution*', [status(thm)], ['2', '60', '80'])).
% 40.71/40.90  thf('82', plain, (~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))),
% 40.71/40.90      inference('simpl_trail', [status(thm)], ['1', '81'])).
% 40.71/40.90  thf('83', plain,
% 40.71/40.90      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))
% 40.71/40.90        | (r1_xboole_0 @ sk_A @ sk_C_1))),
% 40.71/40.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 40.71/40.90  thf('84', plain,
% 40.71/40.90      (((r1_xboole_0 @ sk_A @ sk_C_1)) <= (((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 40.71/40.90      inference('split', [status(esa)], ['83'])).
% 40.71/40.90  thf('85', plain,
% 40.71/40.90      (![X8 : $i, X9 : $i]:
% 40.71/40.90         (((k3_xboole_0 @ X8 @ X9) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 40.71/40.90      inference('cnf', [status(esa)], [d7_xboole_0])).
% 40.71/40.90  thf('86', plain,
% 40.71/40.90      ((((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0)))
% 40.71/40.90         <= (((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 40.71/40.90      inference('sup-', [status(thm)], ['84', '85'])).
% 40.71/40.90  thf('87', plain,
% 40.71/40.90      (((r1_xboole_0 @ sk_A @ sk_C_1)) | 
% 40.71/40.90       ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 40.71/40.90      inference('split', [status(esa)], ['83'])).
% 40.71/40.90  thf('88', plain, (((r1_xboole_0 @ sk_A @ sk_C_1))),
% 40.71/40.90      inference('sat_resolution*', [status(thm)], ['2', '60', '80', '87'])).
% 40.71/40.90  thf('89', plain, (((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))),
% 40.71/40.90      inference('simpl_trail', [status(thm)], ['86', '88'])).
% 40.71/40.90  thf('90', plain,
% 40.71/40.90      (((r1_xboole_0 @ sk_A @ sk_B)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 40.71/40.90      inference('split', [status(esa)], ['3'])).
% 40.71/40.90  thf('91', plain,
% 40.71/40.90      (![X18 : $i, X19 : $i, X20 : $i]:
% 40.71/40.90         ((k4_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X20)
% 40.71/40.90           = (k4_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20)))),
% 40.71/40.90      inference('cnf', [status(esa)], [t41_xboole_1])).
% 40.71/40.90  thf('92', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 40.71/40.90      inference('cnf', [status(esa)], [t3_boole])).
% 40.71/40.90  thf('93', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i]:
% 40.71/40.90         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ k1_xboole_0))
% 40.71/40.90           = (k4_xboole_0 @ X1 @ X0))),
% 40.71/40.90      inference('sup+', [status(thm)], ['91', '92'])).
% 40.71/40.90  thf('94', plain,
% 40.71/40.90      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 40.71/40.90      inference('sup+', [status(thm)], ['35', '36'])).
% 40.71/40.90  thf('95', plain,
% 40.71/40.90      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 40.71/40.90      inference('sup-', [status(thm)], ['18', '19'])).
% 40.71/40.90  thf('96', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 40.71/40.90      inference('demod', [status(thm)], ['94', '95'])).
% 40.71/40.90  thf('97', plain,
% 40.71/40.90      (![X0 : $i]:
% 40.71/40.90         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0) = (k1_xboole_0))),
% 40.71/40.90      inference('sup+', [status(thm)], ['93', '96'])).
% 40.71/40.90  thf('98', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.71/40.90         ((r1_xboole_0 @ X0 @ X1)
% 40.71/40.90          | (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 40.71/40.90          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X2)))),
% 40.71/40.90      inference('sup-', [status(thm)], ['64', '65'])).
% 40.71/40.90  thf('99', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i]:
% 40.71/40.90         ((r2_hidden @ (sk_C @ X1 @ (k2_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 40.71/40.90           k1_xboole_0)
% 40.71/40.90          | (r2_hidden @ (sk_C @ X1 @ (k2_xboole_0 @ X0 @ k1_xboole_0)) @ X0)
% 40.71/40.90          | (r1_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X1))),
% 40.71/40.90      inference('sup+', [status(thm)], ['97', '98'])).
% 40.71/40.90  thf('100', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 40.71/40.90      inference('condensation', [status(thm)], ['14'])).
% 40.71/40.90  thf('101', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i]:
% 40.71/40.90         ((r1_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X1)
% 40.71/40.90          | (r2_hidden @ (sk_C @ X1 @ (k2_xboole_0 @ X0 @ k1_xboole_0)) @ X0))),
% 40.71/40.90      inference('clc', [status(thm)], ['99', '100'])).
% 40.71/40.90  thf('102', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.71/40.90         ((r1_xboole_0 @ X1 @ X0)
% 40.71/40.90          | ~ (r1_xboole_0 @ X0 @ X2)
% 40.71/40.90          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 40.71/40.90      inference('sup-', [status(thm)], ['70', '71'])).
% 40.71/40.90  thf('103', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i]:
% 40.71/40.90         ((r1_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X1)
% 40.71/40.90          | ~ (r1_xboole_0 @ X1 @ X0)
% 40.71/40.90          | (r1_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X1))),
% 40.71/40.90      inference('sup-', [status(thm)], ['101', '102'])).
% 40.71/40.90  thf('104', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i]:
% 40.71/40.90         (~ (r1_xboole_0 @ X1 @ X0)
% 40.71/40.90          | (r1_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X1))),
% 40.71/40.90      inference('simplify', [status(thm)], ['103'])).
% 40.71/40.90  thf('105', plain,
% 40.71/40.90      (((r1_xboole_0 @ (k2_xboole_0 @ sk_B @ k1_xboole_0) @ sk_A))
% 40.71/40.90         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 40.71/40.90      inference('sup-', [status(thm)], ['90', '104'])).
% 40.71/40.90  thf('106', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 40.71/40.90      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 40.71/40.90  thf('107', plain,
% 40.71/40.90      (((r1_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ sk_B) @ sk_A))
% 40.71/40.90         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 40.71/40.90      inference('demod', [status(thm)], ['105', '106'])).
% 40.71/40.90  thf('108', plain,
% 40.71/40.90      (![X13 : $i, X14 : $i]:
% 40.71/40.90         ((r1_xboole_0 @ X13 @ X14) | (r2_hidden @ (sk_C @ X14 @ X13) @ X13))),
% 40.71/40.90      inference('cnf', [status(esa)], [t3_xboole_0])).
% 40.71/40.90  thf('109', plain,
% 40.71/40.90      (![X3 : $i, X4 : $i, X6 : $i]:
% 40.71/40.90         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 40.71/40.90      inference('simplify', [status(thm)], ['29'])).
% 40.71/40.90  thf('110', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.71/40.90         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 40.71/40.90          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 40.71/40.90      inference('sup-', [status(thm)], ['108', '109'])).
% 40.71/40.90  thf('111', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.71/40.90         ((r1_xboole_0 @ X1 @ X0)
% 40.71/40.90          | ~ (r1_xboole_0 @ X0 @ X2)
% 40.71/40.90          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 40.71/40.90      inference('sup-', [status(thm)], ['70', '71'])).
% 40.71/40.90  thf('112', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.71/40.90         ((r1_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)
% 40.71/40.90          | ~ (r1_xboole_0 @ X2 @ X0)
% 40.71/40.90          | (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2))),
% 40.71/40.90      inference('sup-', [status(thm)], ['110', '111'])).
% 40.71/40.90  thf('113', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.71/40.90         (~ (r1_xboole_0 @ X2 @ X0)
% 40.71/40.90          | (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2))),
% 40.71/40.90      inference('simplify', [status(thm)], ['112'])).
% 40.71/40.90  thf('114', plain,
% 40.71/40.90      ((![X0 : $i]:
% 40.71/40.90          (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ 
% 40.71/40.90           (k2_xboole_0 @ k1_xboole_0 @ sk_B)))
% 40.71/40.90         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 40.71/40.90      inference('sup-', [status(thm)], ['107', '113'])).
% 40.71/40.90  thf('115', plain,
% 40.71/40.90      (((r1_xboole_0 @ sk_A @ sk_B)) | 
% 40.71/40.90       ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 40.71/40.90      inference('split', [status(esa)], ['3'])).
% 40.71/40.90  thf('116', plain, (((r1_xboole_0 @ sk_A @ sk_B))),
% 40.71/40.90      inference('sat_resolution*', [status(thm)], ['2', '60', '80', '115'])).
% 40.71/40.90  thf('117', plain,
% 40.71/40.90      (![X0 : $i]:
% 40.71/40.90         (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ 
% 40.71/40.90          (k2_xboole_0 @ k1_xboole_0 @ sk_B))),
% 40.71/40.90      inference('simpl_trail', [status(thm)], ['114', '116'])).
% 40.71/40.90  thf('118', plain,
% 40.71/40.90      (![X3 : $i, X4 : $i, X7 : $i]:
% 40.71/40.90         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 40.71/40.90          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 40.71/40.90          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 40.71/40.90      inference('cnf', [status(esa)], [d5_xboole_0])).
% 40.71/40.90  thf('119', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i]:
% 40.71/40.90         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 40.71/40.90          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 40.71/40.90      inference('eq_fact', [status(thm)], ['118'])).
% 40.71/40.90  thf('120', plain,
% 40.71/40.90      (![X3 : $i, X4 : $i, X7 : $i]:
% 40.71/40.90         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 40.71/40.90          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 40.71/40.90          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 40.71/40.90          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 40.71/40.90      inference('cnf', [status(esa)], [d5_xboole_0])).
% 40.71/40.90  thf('121', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i]:
% 40.71/40.90         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 40.71/40.90          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 40.71/40.90          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 40.71/40.90          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 40.71/40.90      inference('sup-', [status(thm)], ['119', '120'])).
% 40.71/40.90  thf('122', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i]:
% 40.71/40.90         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 40.71/40.90          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 40.71/40.90          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 40.71/40.90      inference('simplify', [status(thm)], ['121'])).
% 40.71/40.90  thf('123', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i]:
% 40.71/40.90         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 40.71/40.90          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 40.71/40.90      inference('eq_fact', [status(thm)], ['118'])).
% 40.71/40.90  thf('124', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i]:
% 40.71/40.90         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 40.71/40.90          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 40.71/40.90      inference('clc', [status(thm)], ['122', '123'])).
% 40.71/40.90  thf('125', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i]:
% 40.71/40.90         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 40.71/40.90          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 40.71/40.90      inference('eq_fact', [status(thm)], ['118'])).
% 40.71/40.90  thf('126', plain,
% 40.71/40.90      (![X13 : $i, X15 : $i, X16 : $i]:
% 40.71/40.90         (~ (r2_hidden @ X15 @ X13)
% 40.71/40.90          | ~ (r2_hidden @ X15 @ X16)
% 40.71/40.90          | ~ (r1_xboole_0 @ X13 @ X16))),
% 40.71/40.90      inference('cnf', [status(esa)], [t3_xboole_0])).
% 40.71/40.90  thf('127', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.71/40.90         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 40.71/40.90          | ~ (r1_xboole_0 @ X0 @ X2)
% 40.71/40.90          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X2))),
% 40.71/40.90      inference('sup-', [status(thm)], ['125', '126'])).
% 40.71/40.90  thf('128', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i]:
% 40.71/40.90         (((X1) = (k4_xboole_0 @ X1 @ X0))
% 40.71/40.90          | ~ (r1_xboole_0 @ X1 @ X0)
% 40.71/40.90          | ((X1) = (k4_xboole_0 @ X1 @ X0)))),
% 40.71/40.90      inference('sup-', [status(thm)], ['124', '127'])).
% 40.71/40.90  thf('129', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i]:
% 40.71/40.90         (~ (r1_xboole_0 @ X1 @ X0) | ((X1) = (k4_xboole_0 @ X1 @ X0)))),
% 40.71/40.90      inference('simplify', [status(thm)], ['128'])).
% 40.71/40.90  thf('130', plain,
% 40.71/40.90      (![X0 : $i]:
% 40.71/40.90         ((k4_xboole_0 @ sk_A @ X0)
% 40.71/40.90           = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ 
% 40.71/40.90              (k2_xboole_0 @ k1_xboole_0 @ sk_B)))),
% 40.71/40.90      inference('sup-', [status(thm)], ['117', '129'])).
% 40.71/40.90  thf('131', plain,
% 40.71/40.90      (![X18 : $i, X19 : $i, X20 : $i]:
% 40.71/40.90         ((k4_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X20)
% 40.71/40.90           = (k4_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20)))),
% 40.71/40.90      inference('cnf', [status(esa)], [t41_xboole_1])).
% 40.71/40.90  thf('132', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i]:
% 40.71/40.90         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ k1_xboole_0))
% 40.71/40.90           = (k4_xboole_0 @ X1 @ X0))),
% 40.71/40.90      inference('sup+', [status(thm)], ['91', '92'])).
% 40.71/40.90  thf('133', plain,
% 40.71/40.90      (![X18 : $i, X19 : $i, X20 : $i]:
% 40.71/40.90         ((k4_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X20)
% 40.71/40.90           = (k4_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20)))),
% 40.71/40.90      inference('cnf', [status(esa)], [t41_xboole_1])).
% 40.71/40.90  thf('134', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.71/40.90         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 40.71/40.90           = (k4_xboole_0 @ X1 @ 
% 40.71/40.90              (k2_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X2)))),
% 40.71/40.90      inference('sup+', [status(thm)], ['132', '133'])).
% 40.71/40.90  thf('135', plain,
% 40.71/40.90      (![X18 : $i, X19 : $i, X20 : $i]:
% 40.71/40.90         ((k4_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X20)
% 40.71/40.90           = (k4_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20)))),
% 40.71/40.90      inference('cnf', [status(esa)], [t41_xboole_1])).
% 40.71/40.90  thf('136', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.71/40.90         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2))
% 40.71/40.90           = (k4_xboole_0 @ X1 @ 
% 40.71/40.90              (k2_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X2)))),
% 40.71/40.90      inference('demod', [status(thm)], ['134', '135'])).
% 40.71/40.90  thf('137', plain,
% 40.71/40.90      (![X18 : $i, X19 : $i, X20 : $i]:
% 40.71/40.90         ((k4_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X20)
% 40.71/40.90           = (k4_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20)))),
% 40.71/40.90      inference('cnf', [status(esa)], [t41_xboole_1])).
% 40.71/40.90  thf('138', plain,
% 40.71/40.90      (![X18 : $i, X19 : $i, X20 : $i]:
% 40.71/40.90         ((k4_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X20)
% 40.71/40.90           = (k4_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20)))),
% 40.71/40.90      inference('cnf', [status(esa)], [t41_xboole_1])).
% 40.71/40.90  thf('139', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 40.71/40.90         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3)
% 40.71/40.90           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k2_xboole_0 @ X0 @ X3)))),
% 40.71/40.90      inference('sup+', [status(thm)], ['137', '138'])).
% 40.71/40.90  thf('140', plain,
% 40.71/40.90      (![X18 : $i, X19 : $i, X20 : $i]:
% 40.71/40.90         ((k4_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X20)
% 40.71/40.90           = (k4_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20)))),
% 40.71/40.90      inference('cnf', [status(esa)], [t41_xboole_1])).
% 40.71/40.90  thf('141', plain,
% 40.71/40.90      (![X18 : $i, X19 : $i, X20 : $i]:
% 40.71/40.90         ((k4_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X20)
% 40.71/40.90           = (k4_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20)))),
% 40.71/40.90      inference('cnf', [status(esa)], [t41_xboole_1])).
% 40.71/40.90  thf('142', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 40.71/40.90         ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X3))
% 40.71/40.90           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X3))))),
% 40.71/40.90      inference('demod', [status(thm)], ['139', '140', '141'])).
% 40.71/40.90  thf('143', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.71/40.90         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2))
% 40.71/40.90           = (k4_xboole_0 @ X1 @ 
% 40.71/40.90              (k2_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X2))))),
% 40.71/40.90      inference('demod', [status(thm)], ['136', '142'])).
% 40.71/40.90  thf('144', plain,
% 40.71/40.90      (![X0 : $i]:
% 40.71/40.90         ((k4_xboole_0 @ sk_A @ X0)
% 40.71/40.90           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_B)))),
% 40.71/40.90      inference('demod', [status(thm)], ['130', '131', '143'])).
% 40.71/40.90  thf('145', plain,
% 40.71/40.90      (![X21 : $i, X22 : $i]:
% 40.71/40.90         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 40.71/40.90           = (k3_xboole_0 @ X21 @ X22))),
% 40.71/40.90      inference('cnf', [status(esa)], [t48_xboole_1])).
% 40.71/40.90  thf('146', plain,
% 40.71/40.90      (![X0 : $i]:
% 40.71/40.90         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ X0))
% 40.71/40.90           = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_B)))),
% 40.71/40.90      inference('sup+', [status(thm)], ['144', '145'])).
% 40.71/40.90  thf('147', plain,
% 40.71/40.90      (![X21 : $i, X22 : $i]:
% 40.71/40.90         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 40.71/40.90           = (k3_xboole_0 @ X21 @ X22))),
% 40.71/40.90      inference('cnf', [status(esa)], [t48_xboole_1])).
% 40.71/40.90  thf('148', plain,
% 40.71/40.90      (![X0 : $i]:
% 40.71/40.90         ((k3_xboole_0 @ sk_A @ X0)
% 40.71/40.90           = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_B)))),
% 40.71/40.90      inference('demod', [status(thm)], ['146', '147'])).
% 40.71/40.90  thf('149', plain,
% 40.71/40.90      (![X8 : $i, X10 : $i]:
% 40.71/40.90         ((r1_xboole_0 @ X8 @ X10)
% 40.71/40.90          | ((k3_xboole_0 @ X8 @ X10) != (k1_xboole_0)))),
% 40.71/40.90      inference('cnf', [status(esa)], [d7_xboole_0])).
% 40.71/40.90  thf('150', plain,
% 40.71/40.90      (![X0 : $i]:
% 40.71/40.90         (((k3_xboole_0 @ sk_A @ X0) != (k1_xboole_0))
% 40.71/40.90          | (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_B)))),
% 40.71/40.90      inference('sup-', [status(thm)], ['148', '149'])).
% 40.71/40.90  thf('151', plain,
% 40.71/40.90      ((((k1_xboole_0) != (k1_xboole_0))
% 40.71/40.90        | (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)))),
% 40.71/40.90      inference('sup-', [status(thm)], ['89', '150'])).
% 40.71/40.90  thf('152', plain,
% 40.71/40.90      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 40.71/40.90      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 40.71/40.90  thf('153', plain,
% 40.71/40.90      ((((k1_xboole_0) != (k1_xboole_0))
% 40.71/40.90        | (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 40.71/40.90      inference('demod', [status(thm)], ['151', '152'])).
% 40.71/40.90  thf('154', plain, ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))),
% 40.71/40.90      inference('simplify', [status(thm)], ['153'])).
% 40.71/40.90  thf('155', plain, ($false), inference('demod', [status(thm)], ['82', '154'])).
% 40.71/40.90  
% 40.71/40.90  % SZS output end Refutation
% 40.71/40.90  
% 40.71/40.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
