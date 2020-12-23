%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Xs5mKXBFkE

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:57 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 274 expanded)
%              Number of leaves         :   21 (  96 expanded)
%              Depth                    :   18
%              Number of atoms          :  700 (1898 expanded)
%              Number of equality atoms :   78 ( 210 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('0',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ X22 @ ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t72_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( ( k2_xboole_0 @ A @ B )
          = ( k2_xboole_0 @ C @ D ) )
        & ( r1_xboole_0 @ C @ A )
        & ( r1_xboole_0 @ D @ B ) )
     => ( C = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( ( k2_xboole_0 @ A @ B )
            = ( k2_xboole_0 @ C @ D ) )
          & ( r1_xboole_0 @ C @ A )
          & ( r1_xboole_0 @ D @ B ) )
       => ( C = B ) ) ),
    inference('cnf.neg',[status(esa)],[t72_xboole_1])).

thf('1',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('3',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      | ~ ( r1_tarski @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_A ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_B @ sk_C ) @ sk_D ),
    inference('sup-',[status(thm)],['0','5'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t67_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ B @ C ) )
     => ( A = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( X19 = k1_xboole_0 )
      | ~ ( r1_tarski @ X19 @ X20 )
      | ~ ( r1_tarski @ X19 @ X21 )
      | ~ ( r1_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t67_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_C )
      = k1_xboole_0 )
    | ~ ( r1_xboole_0 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    r1_xboole_0 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('12',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('13',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['11','12'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('15',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('17',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r1_xboole_0 @ sk_B @ sk_D ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['10','18'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('21',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('23',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ X22 @ ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('29',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('34',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('38',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','44'])).

thf('46',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( ( k4_xboole_0 @ X7 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('52',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['32','56'])).

thf('58',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('59',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ X22 @ ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('60',plain,(
    r1_tarski @ sk_C @ ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('62',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      | ~ ( r1_tarski @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_C @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('66',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('69',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('71',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( ( k4_xboole_0 @ X7 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_C @ ( k4_xboole_0 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    r1_tarski @ sk_C @ ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('76',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_C @ sk_A ) )
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('78',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['66','78'])).

thf('80',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('81',plain,
    ( ( k4_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['32','56'])).

thf('83',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('84',plain,
    ( sk_C
    = ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,(
    sk_B = sk_C ),
    inference(demod,[status(thm)],['21','57','84'])).

thf('86',plain,(
    sk_C != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['85','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Xs5mKXBFkE
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:22:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.43/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.62  % Solved by: fo/fo7.sh
% 0.43/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.62  % done 501 iterations in 0.173s
% 0.43/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.62  % SZS output start Refutation
% 0.43/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.43/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.43/0.62  thf(sk_D_type, type, sk_D: $i).
% 0.43/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.43/0.62  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.43/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.43/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.43/0.62  thf(t7_xboole_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.43/0.62  thf('0', plain,
% 0.43/0.62      (![X22 : $i, X23 : $i]: (r1_tarski @ X22 @ (k2_xboole_0 @ X22 @ X23))),
% 0.43/0.62      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.43/0.62  thf(t72_xboole_1, conjecture,
% 0.43/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.62     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.43/0.62         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.43/0.62       ( ( C ) = ( B ) ) ))).
% 0.43/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.62    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.62        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.43/0.62            ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.43/0.62          ( ( C ) = ( B ) ) ) )),
% 0.43/0.62    inference('cnf.neg', [status(esa)], [t72_xboole_1])).
% 0.43/0.62  thf('1', plain,
% 0.43/0.62      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(commutativity_k2_xboole_0, axiom,
% 0.43/0.62    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.43/0.62  thf('2', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.43/0.62      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.43/0.62  thf('3', plain,
% 0.43/0.62      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.43/0.62      inference('demod', [status(thm)], ['1', '2'])).
% 0.43/0.62  thf(t43_xboole_1, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i]:
% 0.43/0.62     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.43/0.62       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.43/0.62  thf('4', plain,
% 0.43/0.62      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.43/0.62         ((r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.43/0.62          | ~ (r1_tarski @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.43/0.62  thf('5', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_A))
% 0.43/0.62          | (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C) @ sk_D))),
% 0.43/0.62      inference('sup-', [status(thm)], ['3', '4'])).
% 0.43/0.62  thf('6', plain, ((r1_tarski @ (k4_xboole_0 @ sk_B @ sk_C) @ sk_D)),
% 0.43/0.62      inference('sup-', [status(thm)], ['0', '5'])).
% 0.43/0.62  thf(t36_xboole_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.43/0.62  thf('7', plain,
% 0.43/0.62      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 0.43/0.62      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.43/0.62  thf(t67_xboole_1, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i]:
% 0.43/0.62     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 0.43/0.62         ( r1_xboole_0 @ B @ C ) ) =>
% 0.43/0.62       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.43/0.62  thf('8', plain,
% 0.43/0.62      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.43/0.62         (((X19) = (k1_xboole_0))
% 0.43/0.62          | ~ (r1_tarski @ X19 @ X20)
% 0.43/0.62          | ~ (r1_tarski @ X19 @ X21)
% 0.43/0.62          | ~ (r1_xboole_0 @ X20 @ X21))),
% 0.43/0.62      inference('cnf', [status(esa)], [t67_xboole_1])).
% 0.43/0.62  thf('9', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.62         (~ (r1_xboole_0 @ X0 @ X2)
% 0.43/0.62          | ~ (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2)
% 0.43/0.62          | ((k4_xboole_0 @ X0 @ X1) = (k1_xboole_0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['7', '8'])).
% 0.43/0.62  thf('10', plain,
% 0.43/0.62      ((((k4_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))
% 0.43/0.62        | ~ (r1_xboole_0 @ sk_B @ sk_D))),
% 0.43/0.62      inference('sup-', [status(thm)], ['6', '9'])).
% 0.43/0.62  thf('11', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(d7_xboole_0, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.43/0.62       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.43/0.62  thf('12', plain,
% 0.43/0.62      (![X4 : $i, X5 : $i]:
% 0.43/0.62         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.43/0.62      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.43/0.62  thf('13', plain, (((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['11', '12'])).
% 0.43/0.62  thf(commutativity_k3_xboole_0, axiom,
% 0.43/0.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.43/0.62  thf('14', plain,
% 0.43/0.62      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.43/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.43/0.62  thf('15', plain, (((k3_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0))),
% 0.43/0.62      inference('demod', [status(thm)], ['13', '14'])).
% 0.43/0.62  thf('16', plain,
% 0.43/0.62      (![X4 : $i, X6 : $i]:
% 0.43/0.62         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 0.43/0.62      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.43/0.62  thf('17', plain,
% 0.43/0.62      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_D))),
% 0.43/0.62      inference('sup-', [status(thm)], ['15', '16'])).
% 0.43/0.62  thf('18', plain, ((r1_xboole_0 @ sk_B @ sk_D)),
% 0.43/0.62      inference('simplify', [status(thm)], ['17'])).
% 0.43/0.62  thf('19', plain, (((k4_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))),
% 0.43/0.62      inference('demod', [status(thm)], ['10', '18'])).
% 0.43/0.62  thf(t48_xboole_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.43/0.62  thf('20', plain,
% 0.43/0.62      (![X17 : $i, X18 : $i]:
% 0.43/0.62         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.43/0.62           = (k3_xboole_0 @ X17 @ X18))),
% 0.43/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.43/0.62  thf('21', plain,
% 0.43/0.62      (((k4_xboole_0 @ sk_B @ k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_C))),
% 0.43/0.62      inference('sup+', [status(thm)], ['19', '20'])).
% 0.43/0.62  thf('22', plain,
% 0.43/0.62      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 0.43/0.62      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.43/0.62  thf(t12_xboole_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.43/0.62  thf('23', plain,
% 0.43/0.62      (![X10 : $i, X11 : $i]:
% 0.43/0.62         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.43/0.62      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.43/0.62  thf('24', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['22', '23'])).
% 0.43/0.62  thf('25', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.43/0.62      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.43/0.62  thf('26', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.43/0.62      inference('demod', [status(thm)], ['24', '25'])).
% 0.43/0.62  thf('27', plain,
% 0.43/0.62      (![X22 : $i, X23 : $i]: (r1_tarski @ X22 @ (k2_xboole_0 @ X22 @ X23))),
% 0.43/0.62      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.43/0.62  thf('28', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.43/0.62      inference('sup+', [status(thm)], ['26', '27'])).
% 0.43/0.62  thf(l32_xboole_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.43/0.62  thf('29', plain,
% 0.43/0.62      (![X7 : $i, X9 : $i]:
% 0.43/0.62         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.43/0.62      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.43/0.62  thf('30', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['28', '29'])).
% 0.43/0.62  thf('31', plain,
% 0.43/0.62      (![X17 : $i, X18 : $i]:
% 0.43/0.62         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.43/0.62           = (k3_xboole_0 @ X17 @ X18))),
% 0.43/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.43/0.62  thf('32', plain,
% 0.43/0.62      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['30', '31'])).
% 0.43/0.62  thf('33', plain,
% 0.43/0.62      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['30', '31'])).
% 0.43/0.62  thf('34', plain,
% 0.43/0.62      (![X17 : $i, X18 : $i]:
% 0.43/0.62         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.43/0.62           = (k3_xboole_0 @ X17 @ X18))),
% 0.43/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.43/0.62  thf('35', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0))
% 0.43/0.62           = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['33', '34'])).
% 0.43/0.62  thf('36', plain,
% 0.43/0.62      (![X17 : $i, X18 : $i]:
% 0.43/0.62         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.43/0.62           = (k3_xboole_0 @ X17 @ X18))),
% 0.43/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.43/0.62  thf('37', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['28', '29'])).
% 0.43/0.62  thf('38', plain,
% 0.43/0.62      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 0.43/0.62      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.43/0.62  thf('39', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.43/0.62      inference('sup+', [status(thm)], ['37', '38'])).
% 0.43/0.62  thf('40', plain,
% 0.43/0.62      (![X7 : $i, X9 : $i]:
% 0.43/0.62         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.43/0.62      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.43/0.62  thf('41', plain,
% 0.43/0.62      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['39', '40'])).
% 0.43/0.62  thf('42', plain,
% 0.43/0.62      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['36', '41'])).
% 0.43/0.62  thf('43', plain,
% 0.43/0.62      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.43/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.43/0.62  thf('44', plain,
% 0.43/0.62      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['42', '43'])).
% 0.43/0.62  thf('45', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.43/0.62      inference('demod', [status(thm)], ['35', '44'])).
% 0.43/0.62  thf('46', plain,
% 0.43/0.62      (![X7 : $i, X8 : $i]:
% 0.43/0.62         ((r1_tarski @ X7 @ X8) | ((k4_xboole_0 @ X7 @ X8) != (k1_xboole_0)))),
% 0.43/0.62      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.43/0.62  thf('47', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (((k1_xboole_0) != (k1_xboole_0))
% 0.43/0.62          | (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['45', '46'])).
% 0.43/0.62  thf('48', plain, (![X0 : $i]: (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X0))),
% 0.43/0.62      inference('simplify', [status(thm)], ['47'])).
% 0.43/0.62  thf('49', plain,
% 0.43/0.62      (![X10 : $i, X11 : $i]:
% 0.43/0.62         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.43/0.62      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.43/0.62  thf('50', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0))
% 0.43/0.62           = (k3_xboole_0 @ X0 @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['48', '49'])).
% 0.43/0.62  thf('51', plain,
% 0.43/0.62      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.43/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.43/0.62  thf('52', plain,
% 0.43/0.62      (![X17 : $i, X18 : $i]:
% 0.43/0.62         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.43/0.62           = (k3_xboole_0 @ X17 @ X18))),
% 0.43/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.43/0.62  thf('53', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.43/0.62      inference('demod', [status(thm)], ['24', '25'])).
% 0.43/0.62  thf('54', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 0.43/0.62      inference('sup+', [status(thm)], ['52', '53'])).
% 0.43/0.62  thf('55', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['51', '54'])).
% 0.43/0.62  thf('56', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.43/0.62      inference('demod', [status(thm)], ['50', '55'])).
% 0.43/0.62  thf('57', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.43/0.62      inference('demod', [status(thm)], ['32', '56'])).
% 0.43/0.62  thf('58', plain,
% 0.43/0.62      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.43/0.62      inference('demod', [status(thm)], ['1', '2'])).
% 0.43/0.62  thf('59', plain,
% 0.43/0.62      (![X22 : $i, X23 : $i]: (r1_tarski @ X22 @ (k2_xboole_0 @ X22 @ X23))),
% 0.43/0.62      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.43/0.62  thf('60', plain, ((r1_tarski @ sk_C @ (k2_xboole_0 @ sk_B @ sk_A))),
% 0.43/0.62      inference('sup+', [status(thm)], ['58', '59'])).
% 0.43/0.62  thf('61', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.43/0.62      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.43/0.62  thf('62', plain,
% 0.43/0.62      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.43/0.62         ((r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.43/0.62          | ~ (r1_tarski @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.43/0.62  thf('63', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.62         (~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.43/0.62          | (r1_tarski @ (k4_xboole_0 @ X2 @ X0) @ X1))),
% 0.43/0.62      inference('sup-', [status(thm)], ['61', '62'])).
% 0.43/0.62  thf('64', plain, ((r1_tarski @ (k4_xboole_0 @ sk_C @ sk_A) @ sk_B)),
% 0.43/0.62      inference('sup-', [status(thm)], ['60', '63'])).
% 0.43/0.62  thf('65', plain,
% 0.43/0.62      (![X7 : $i, X9 : $i]:
% 0.43/0.62         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.43/0.62      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.43/0.62  thf('66', plain,
% 0.43/0.62      (((k4_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['64', '65'])).
% 0.43/0.62  thf('67', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('68', plain,
% 0.43/0.62      (![X4 : $i, X5 : $i]:
% 0.43/0.62         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.43/0.62      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.43/0.62  thf('69', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['67', '68'])).
% 0.43/0.62  thf('70', plain,
% 0.43/0.62      (![X17 : $i, X18 : $i]:
% 0.43/0.62         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.43/0.62           = (k3_xboole_0 @ X17 @ X18))),
% 0.43/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.43/0.62  thf('71', plain,
% 0.43/0.62      (![X7 : $i, X8 : $i]:
% 0.43/0.62         ((r1_tarski @ X7 @ X8) | ((k4_xboole_0 @ X7 @ X8) != (k1_xboole_0)))),
% 0.43/0.62      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.43/0.62  thf('72', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 0.43/0.62          | (r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['70', '71'])).
% 0.43/0.62  thf('73', plain,
% 0.43/0.62      ((((k1_xboole_0) != (k1_xboole_0))
% 0.43/0.62        | (r1_tarski @ sk_C @ (k4_xboole_0 @ sk_C @ sk_A)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['69', '72'])).
% 0.43/0.62  thf('74', plain, ((r1_tarski @ sk_C @ (k4_xboole_0 @ sk_C @ sk_A))),
% 0.43/0.62      inference('simplify', [status(thm)], ['73'])).
% 0.43/0.62  thf('75', plain,
% 0.43/0.62      (![X10 : $i, X11 : $i]:
% 0.43/0.62         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.43/0.62      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.43/0.62  thf('76', plain,
% 0.43/0.62      (((k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_C @ sk_A))
% 0.43/0.62         = (k4_xboole_0 @ sk_C @ sk_A))),
% 0.43/0.62      inference('sup-', [status(thm)], ['74', '75'])).
% 0.43/0.62  thf('77', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.43/0.62      inference('demod', [status(thm)], ['24', '25'])).
% 0.43/0.62  thf('78', plain, (((sk_C) = (k4_xboole_0 @ sk_C @ sk_A))),
% 0.43/0.62      inference('demod', [status(thm)], ['76', '77'])).
% 0.43/0.62  thf('79', plain, (((k4_xboole_0 @ sk_C @ sk_B) = (k1_xboole_0))),
% 0.43/0.62      inference('demod', [status(thm)], ['66', '78'])).
% 0.43/0.62  thf('80', plain,
% 0.43/0.62      (![X17 : $i, X18 : $i]:
% 0.43/0.62         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.43/0.62           = (k3_xboole_0 @ X17 @ X18))),
% 0.43/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.43/0.62  thf('81', plain,
% 0.43/0.62      (((k4_xboole_0 @ sk_C @ k1_xboole_0) = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.43/0.62      inference('sup+', [status(thm)], ['79', '80'])).
% 0.43/0.62  thf('82', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.43/0.62      inference('demod', [status(thm)], ['32', '56'])).
% 0.43/0.62  thf('83', plain,
% 0.43/0.62      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.43/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.43/0.62  thf('84', plain, (((sk_C) = (k3_xboole_0 @ sk_B @ sk_C))),
% 0.43/0.62      inference('demod', [status(thm)], ['81', '82', '83'])).
% 0.43/0.62  thf('85', plain, (((sk_B) = (sk_C))),
% 0.43/0.62      inference('demod', [status(thm)], ['21', '57', '84'])).
% 0.43/0.62  thf('86', plain, (((sk_C) != (sk_B))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('87', plain, ($false),
% 0.43/0.62      inference('simplify_reflect-', [status(thm)], ['85', '86'])).
% 0.43/0.62  
% 0.43/0.62  % SZS output end Refutation
% 0.43/0.62  
% 0.45/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
