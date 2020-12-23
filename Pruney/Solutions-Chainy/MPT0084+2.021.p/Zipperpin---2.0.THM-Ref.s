%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FfgbvBD8nh

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:21 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 215 expanded)
%              Number of leaves         :   23 (  79 expanded)
%              Depth                    :   19
%              Number of atoms          :  693 (1520 expanded)
%              Number of equality atoms :   50 ( 136 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t77_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ( r1_tarski @ A @ C )
          & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ k1_xboole_0 )
    = ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('8',plain,(
    ! [X16: $i] :
      ( ( k3_xboole_0 @ X16 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('9',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ ( k4_xboole_0 @ X21 @ X22 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X16: $i] :
      ( ( k3_xboole_0 @ X16 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('12',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('14',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['7','16'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('19',plain,
    ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) )
    = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('21',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X16: $i] :
      ( ( k3_xboole_0 @ X16 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('25',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k3_xboole_0 @ X11 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('26',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('28',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('30',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('33',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('35',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','38'])).

thf('40',plain,
    ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ sk_B ) @ k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','39'])).

thf('41',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k3_xboole_0 @ X11 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('43',plain,(
    ! [X16: $i] :
      ( ( k3_xboole_0 @ X16 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('44',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    r1_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41','42','46'])).

thf('48',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('49',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k3_xboole_0 @ X11 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    r1_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['47','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('55',plain,(
    r1_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    r1_tarski @ sk_A @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('62',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_C_1 )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['60','61'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('63',plain,(
    ! [X23: $i,X24: $i,X26: $i] :
      ( ( r1_xboole_0 @ X23 @ X24 )
      | ~ ( r1_xboole_0 @ X23 @ ( k2_xboole_0 @ X24 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_C_1 )
      | ( r1_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['59','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('67',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('70',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k3_xboole_0 @ X11 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('71',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','73'])).

thf('75',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['65','74'])).

thf('76',plain,(
    $false ),
    inference(demod,[status(thm)],['0','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FfgbvBD8nh
% 0.11/0.32  % Computer   : n016.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 10:38:04 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running portfolio for 600 s
% 0.11/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.33  % Number of cores: 8
% 0.11/0.33  % Python version: Python 3.6.8
% 0.11/0.33  % Running in FO mode
% 0.44/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.66  % Solved by: fo/fo7.sh
% 0.44/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.66  % done 480 iterations in 0.262s
% 0.44/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.66  % SZS output start Refutation
% 0.44/0.66  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.44/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.66  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.44/0.66  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.44/0.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.44/0.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.44/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.66  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.44/0.66  thf(t77_xboole_1, conjecture,
% 0.44/0.66    (![A:$i,B:$i,C:$i]:
% 0.44/0.66     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.44/0.66          ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 0.44/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.66    (~( ![A:$i,B:$i,C:$i]:
% 0.44/0.66        ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.44/0.66             ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )),
% 0.44/0.66    inference('cnf.neg', [status(esa)], [t77_xboole_1])).
% 0.44/0.66  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('1', plain, ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf(d7_xboole_0, axiom,
% 0.44/0.66    (![A:$i,B:$i]:
% 0.44/0.66     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.44/0.66       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.44/0.66  thf('2', plain,
% 0.44/0.66      (![X2 : $i, X3 : $i]:
% 0.44/0.66         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.44/0.66      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.44/0.66  thf('3', plain,
% 0.44/0.66      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1)) = (k1_xboole_0))),
% 0.44/0.66      inference('sup-', [status(thm)], ['1', '2'])).
% 0.44/0.66  thf(commutativity_k3_xboole_0, axiom,
% 0.44/0.66    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.44/0.66  thf('4', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.44/0.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.44/0.66  thf(t47_xboole_1, axiom,
% 0.44/0.66    (![A:$i,B:$i]:
% 0.44/0.66     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.44/0.66  thf('5', plain,
% 0.44/0.66      (![X17 : $i, X18 : $i]:
% 0.44/0.66         ((k4_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18))
% 0.44/0.66           = (k4_xboole_0 @ X17 @ X18))),
% 0.44/0.66      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.44/0.66  thf('6', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.44/0.66           = (k4_xboole_0 @ X0 @ X1))),
% 0.44/0.66      inference('sup+', [status(thm)], ['4', '5'])).
% 0.44/0.66  thf('7', plain,
% 0.44/0.66      (((k4_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C_1) @ k1_xboole_0)
% 0.44/0.66         = (k4_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C_1) @ sk_A))),
% 0.44/0.66      inference('sup+', [status(thm)], ['3', '6'])).
% 0.44/0.66  thf(t2_boole, axiom,
% 0.44/0.66    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.44/0.66  thf('8', plain,
% 0.44/0.66      (![X16 : $i]: ((k3_xboole_0 @ X16 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.66      inference('cnf', [status(esa)], [t2_boole])).
% 0.44/0.66  thf(t51_xboole_1, axiom,
% 0.44/0.66    (![A:$i,B:$i]:
% 0.44/0.66     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.44/0.66       ( A ) ))).
% 0.44/0.66  thf('9', plain,
% 0.44/0.66      (![X21 : $i, X22 : $i]:
% 0.44/0.66         ((k2_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ (k4_xboole_0 @ X21 @ X22))
% 0.44/0.66           = (X21))),
% 0.44/0.66      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.44/0.66  thf('10', plain,
% 0.44/0.66      (![X0 : $i]:
% 0.44/0.66         ((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 0.44/0.66      inference('sup+', [status(thm)], ['8', '9'])).
% 0.44/0.66  thf('11', plain,
% 0.44/0.66      (![X16 : $i]: ((k3_xboole_0 @ X16 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.66      inference('cnf', [status(esa)], [t2_boole])).
% 0.44/0.66  thf(t17_xboole_1, axiom,
% 0.44/0.66    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.44/0.66  thf('12', plain,
% 0.44/0.66      (![X14 : $i, X15 : $i]: (r1_tarski @ (k3_xboole_0 @ X14 @ X15) @ X14)),
% 0.44/0.66      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.44/0.66  thf('13', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.44/0.66      inference('sup+', [status(thm)], ['11', '12'])).
% 0.44/0.66  thf(t12_xboole_1, axiom,
% 0.44/0.66    (![A:$i,B:$i]:
% 0.44/0.66     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.44/0.66  thf('14', plain,
% 0.44/0.66      (![X9 : $i, X10 : $i]:
% 0.44/0.66         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 0.44/0.66      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.44/0.66  thf('15', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.44/0.66      inference('sup-', [status(thm)], ['13', '14'])).
% 0.44/0.66  thf('16', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.44/0.66      inference('demod', [status(thm)], ['10', '15'])).
% 0.44/0.66  thf('17', plain,
% 0.44/0.66      (((k3_xboole_0 @ sk_B @ sk_C_1)
% 0.44/0.66         = (k4_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C_1) @ sk_A))),
% 0.44/0.66      inference('demod', [status(thm)], ['7', '16'])).
% 0.44/0.66  thf(t48_xboole_1, axiom,
% 0.44/0.66    (![A:$i,B:$i]:
% 0.44/0.66     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.44/0.66  thf('18', plain,
% 0.44/0.66      (![X19 : $i, X20 : $i]:
% 0.44/0.66         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.44/0.66           = (k3_xboole_0 @ X19 @ X20))),
% 0.44/0.66      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.44/0.66  thf('19', plain,
% 0.44/0.66      (((k4_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C_1) @ 
% 0.44/0.66         (k3_xboole_0 @ sk_B @ sk_C_1))
% 0.44/0.66         = (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C_1) @ sk_A))),
% 0.44/0.66      inference('sup+', [status(thm)], ['17', '18'])).
% 0.44/0.66  thf('20', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.44/0.66      inference('demod', [status(thm)], ['10', '15'])).
% 0.44/0.66  thf('21', plain,
% 0.44/0.66      (![X19 : $i, X20 : $i]:
% 0.44/0.66         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.44/0.66           = (k3_xboole_0 @ X19 @ X20))),
% 0.44/0.66      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.44/0.66  thf('22', plain,
% 0.44/0.66      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.44/0.66      inference('sup+', [status(thm)], ['20', '21'])).
% 0.44/0.66  thf('23', plain,
% 0.44/0.66      (![X16 : $i]: ((k3_xboole_0 @ X16 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.66      inference('cnf', [status(esa)], [t2_boole])).
% 0.44/0.66  thf('24', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.44/0.66      inference('demod', [status(thm)], ['22', '23'])).
% 0.44/0.66  thf(t16_xboole_1, axiom,
% 0.44/0.66    (![A:$i,B:$i,C:$i]:
% 0.44/0.66     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.44/0.66       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.44/0.66  thf('25', plain,
% 0.44/0.66      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.44/0.66         ((k3_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13)
% 0.44/0.66           = (k3_xboole_0 @ X11 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.44/0.66      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.44/0.66  thf('26', plain,
% 0.44/0.66      (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C_1 @ sk_A)))),
% 0.44/0.66      inference('demod', [status(thm)], ['19', '24', '25'])).
% 0.44/0.66  thf('27', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.44/0.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.44/0.66  thf(t4_xboole_0, axiom,
% 0.44/0.66    (![A:$i,B:$i]:
% 0.44/0.66     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.44/0.66            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.44/0.66       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.44/0.66            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.44/0.66  thf('28', plain,
% 0.44/0.66      (![X5 : $i, X6 : $i]:
% 0.44/0.66         ((r1_xboole_0 @ X5 @ X6)
% 0.44/0.66          | (r2_hidden @ (sk_C @ X6 @ X5) @ (k3_xboole_0 @ X5 @ X6)))),
% 0.44/0.66      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.44/0.66  thf('29', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.44/0.66      inference('demod', [status(thm)], ['22', '23'])).
% 0.44/0.66  thf('30', plain,
% 0.44/0.66      (![X19 : $i, X20 : $i]:
% 0.44/0.66         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.44/0.66           = (k3_xboole_0 @ X19 @ X20))),
% 0.44/0.66      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.44/0.66  thf('31', plain,
% 0.44/0.66      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.44/0.66      inference('sup+', [status(thm)], ['29', '30'])).
% 0.44/0.66  thf('32', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.44/0.66      inference('demod', [status(thm)], ['10', '15'])).
% 0.44/0.66  thf('33', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.44/0.66      inference('demod', [status(thm)], ['31', '32'])).
% 0.44/0.66  thf('34', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.44/0.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.44/0.66  thf('35', plain,
% 0.44/0.66      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.44/0.66         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.44/0.66          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.44/0.66      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.44/0.66  thf('36', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.66         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.44/0.66          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.44/0.66      inference('sup-', [status(thm)], ['34', '35'])).
% 0.44/0.66  thf('37', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.44/0.66      inference('sup-', [status(thm)], ['33', '36'])).
% 0.44/0.66  thf('38', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         ((r1_xboole_0 @ X1 @ X0)
% 0.44/0.66          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.44/0.66      inference('sup-', [status(thm)], ['28', '37'])).
% 0.44/0.66  thf('39', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         (~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 0.44/0.66          | (r1_xboole_0 @ X0 @ X1))),
% 0.44/0.66      inference('sup-', [status(thm)], ['27', '38'])).
% 0.44/0.66  thf('40', plain,
% 0.44/0.66      ((~ (r1_xboole_0 @ 
% 0.44/0.66           (k3_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ sk_B) @ k1_xboole_0)
% 0.44/0.66        | (r1_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C_1 @ sk_A)))),
% 0.44/0.66      inference('sup-', [status(thm)], ['26', '39'])).
% 0.44/0.66  thf('41', plain,
% 0.44/0.66      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.44/0.66         ((k3_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13)
% 0.44/0.66           = (k3_xboole_0 @ X11 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.44/0.66      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.44/0.66  thf('42', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.44/0.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.44/0.66  thf('43', plain,
% 0.44/0.66      (![X16 : $i]: ((k3_xboole_0 @ X16 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.66      inference('cnf', [status(esa)], [t2_boole])).
% 0.44/0.66  thf('44', plain,
% 0.44/0.66      (![X2 : $i, X4 : $i]:
% 0.44/0.66         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.44/0.66      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.44/0.66  thf('45', plain,
% 0.44/0.66      (![X0 : $i]:
% 0.44/0.66         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.44/0.66      inference('sup-', [status(thm)], ['43', '44'])).
% 0.44/0.66  thf('46', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.44/0.66      inference('simplify', [status(thm)], ['45'])).
% 0.44/0.66  thf('47', plain, ((r1_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 0.44/0.66      inference('demod', [status(thm)], ['40', '41', '42', '46'])).
% 0.44/0.66  thf('48', plain,
% 0.44/0.66      (![X5 : $i, X6 : $i]:
% 0.44/0.66         ((r1_xboole_0 @ X5 @ X6)
% 0.44/0.66          | (r2_hidden @ (sk_C @ X6 @ X5) @ (k3_xboole_0 @ X5 @ X6)))),
% 0.44/0.66      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.44/0.66  thf('49', plain,
% 0.44/0.66      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.44/0.66         ((k3_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13)
% 0.44/0.66           = (k3_xboole_0 @ X11 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.44/0.66      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.44/0.66  thf('50', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.66         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.44/0.66          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.44/0.66      inference('sup-', [status(thm)], ['34', '35'])).
% 0.44/0.66  thf('51', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.44/0.66         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.44/0.66          | ~ (r1_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1)))),
% 0.44/0.66      inference('sup-', [status(thm)], ['49', '50'])).
% 0.44/0.66  thf('52', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.66         ((r1_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.44/0.66          | ~ (r1_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1)))),
% 0.44/0.66      inference('sup-', [status(thm)], ['48', '51'])).
% 0.44/0.66  thf('53', plain, ((r1_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ sk_A @ sk_B))),
% 0.44/0.66      inference('sup-', [status(thm)], ['47', '52'])).
% 0.44/0.66  thf('54', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.44/0.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.44/0.66  thf('55', plain, ((r1_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ sk_B @ sk_A))),
% 0.44/0.66      inference('demod', [status(thm)], ['53', '54'])).
% 0.44/0.66  thf('56', plain,
% 0.44/0.66      (![X5 : $i, X6 : $i]:
% 0.44/0.66         ((r1_xboole_0 @ X5 @ X6)
% 0.44/0.66          | (r2_hidden @ (sk_C @ X6 @ X5) @ (k3_xboole_0 @ X5 @ X6)))),
% 0.44/0.66      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.44/0.66  thf('57', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.66         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.44/0.66          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.44/0.66      inference('sup-', [status(thm)], ['34', '35'])).
% 0.44/0.66  thf('58', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.44/0.66      inference('sup-', [status(thm)], ['56', '57'])).
% 0.44/0.66  thf('59', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_C_1)),
% 0.44/0.66      inference('sup-', [status(thm)], ['55', '58'])).
% 0.44/0.66  thf('60', plain, ((r1_tarski @ sk_A @ sk_C_1)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('61', plain,
% 0.44/0.66      (![X9 : $i, X10 : $i]:
% 0.44/0.66         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 0.44/0.66      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.44/0.66  thf('62', plain, (((k2_xboole_0 @ sk_A @ sk_C_1) = (sk_C_1))),
% 0.44/0.66      inference('sup-', [status(thm)], ['60', '61'])).
% 0.44/0.66  thf(t70_xboole_1, axiom,
% 0.44/0.66    (![A:$i,B:$i,C:$i]:
% 0.44/0.66     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.44/0.66            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.44/0.66       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.44/0.66            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.44/0.66  thf('63', plain,
% 0.44/0.66      (![X23 : $i, X24 : $i, X26 : $i]:
% 0.44/0.66         ((r1_xboole_0 @ X23 @ X24)
% 0.44/0.66          | ~ (r1_xboole_0 @ X23 @ (k2_xboole_0 @ X24 @ X26)))),
% 0.44/0.66      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.44/0.66  thf('64', plain,
% 0.44/0.66      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ sk_C_1) | (r1_xboole_0 @ X0 @ sk_A))),
% 0.44/0.66      inference('sup-', [status(thm)], ['62', '63'])).
% 0.44/0.66  thf('65', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_A)),
% 0.44/0.66      inference('sup-', [status(thm)], ['59', '64'])).
% 0.44/0.66  thf('66', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.44/0.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.44/0.66  thf('67', plain,
% 0.44/0.66      (![X5 : $i, X6 : $i]:
% 0.44/0.66         ((r1_xboole_0 @ X5 @ X6)
% 0.44/0.66          | (r2_hidden @ (sk_C @ X6 @ X5) @ (k3_xboole_0 @ X5 @ X6)))),
% 0.44/0.66      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.44/0.66  thf('68', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         ((r2_hidden @ (sk_C @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.44/0.66          | (r1_xboole_0 @ X0 @ X1))),
% 0.44/0.66      inference('sup+', [status(thm)], ['66', '67'])).
% 0.44/0.66  thf('69', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.44/0.66      inference('demod', [status(thm)], ['31', '32'])).
% 0.44/0.66  thf('70', plain,
% 0.44/0.66      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.44/0.66         ((k3_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13)
% 0.44/0.66           = (k3_xboole_0 @ X11 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.44/0.66      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.44/0.66  thf('71', plain,
% 0.44/0.66      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.44/0.66         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.44/0.66          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.44/0.66      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.44/0.66  thf('72', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.44/0.66         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.44/0.66          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 0.44/0.66      inference('sup-', [status(thm)], ['70', '71'])).
% 0.44/0.66  thf('73', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.66         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.44/0.66          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.44/0.66      inference('sup-', [status(thm)], ['69', '72'])).
% 0.44/0.66  thf('74', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         ((r1_xboole_0 @ X0 @ X1)
% 0.44/0.66          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.44/0.66      inference('sup-', [status(thm)], ['68', '73'])).
% 0.44/0.66  thf('75', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.44/0.66      inference('sup-', [status(thm)], ['65', '74'])).
% 0.44/0.66  thf('76', plain, ($false), inference('demod', [status(thm)], ['0', '75'])).
% 0.44/0.66  
% 0.44/0.66  % SZS output end Refutation
% 0.44/0.66  
% 0.44/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
