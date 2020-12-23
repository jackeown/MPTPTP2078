%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dUVNSvf7QP

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:34 EST 2020

% Result     : Theorem 0.80s
% Output     : Refutation 0.80s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 231 expanded)
%              Number of leaves         :   24 (  85 expanded)
%              Depth                    :   16
%              Number of atoms          :  699 (1716 expanded)
%              Number of equality atoms :   64 ( 159 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t63_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_xboole_0 @ B @ C ) )
       => ( r1_xboole_0 @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t63_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('3',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('6',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('7',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('9',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('11',plain,(
    r1_xboole_0 @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('12',plain,(
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

thf('13',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['11','14'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('16',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ ( k4_xboole_0 @ X21 @ X22 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('17',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('18',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('19',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ ( k4_xboole_0 @ X21 @ X22 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_C_1 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['17','22'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B_1 @ X0 )
      = ( k4_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B_1 @ X0 )
      = ( k4_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['10','25'])).

thf('27',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('28',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B_1 @ X0 ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ X0 ) @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['26','31'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('33',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('34',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('35',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('36',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','33','42','43'])).

thf('45',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('47',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('50',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_B_1 @ X0 ) ) @ k1_xboole_0 )
      | ( r1_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','33','42','43'])).

thf('56',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('57',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','52'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('64',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['11','14'])).

thf('67',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    r1_xboole_0 @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['65','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['62','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ X0 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['8','74'])).

thf('76',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_A ),
    inference('sup+',[status(thm)],['7','75'])).

thf('77',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('78',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('79',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['76','81'])).

thf('83',plain,(
    $false ),
    inference(demod,[status(thm)],['0','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dUVNSvf7QP
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:08:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.80/0.99  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.80/0.99  % Solved by: fo/fo7.sh
% 0.80/0.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.80/0.99  % done 1411 iterations in 0.535s
% 0.80/0.99  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.80/0.99  % SZS output start Refutation
% 0.80/0.99  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.80/0.99  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.80/0.99  thf(sk_B_type, type, sk_B: $i > $i).
% 0.80/0.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.80/0.99  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.80/0.99  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.80/0.99  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.80/0.99  thf(sk_A_type, type, sk_A: $i).
% 0.80/0.99  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.80/0.99  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.80/0.99  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.80/0.99  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.80/0.99  thf(t63_xboole_1, conjecture,
% 0.80/0.99    (![A:$i,B:$i,C:$i]:
% 0.80/0.99     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.80/0.99       ( r1_xboole_0 @ A @ C ) ))).
% 0.80/0.99  thf(zf_stmt_0, negated_conjecture,
% 0.80/0.99    (~( ![A:$i,B:$i,C:$i]:
% 0.80/0.99        ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.80/0.99          ( r1_xboole_0 @ A @ C ) ) )),
% 0.80/0.99    inference('cnf.neg', [status(esa)], [t63_xboole_1])).
% 0.80/0.99  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_C_1)),
% 0.80/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/0.99  thf('1', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.80/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/0.99  thf(l32_xboole_1, axiom,
% 0.80/0.99    (![A:$i,B:$i]:
% 0.80/0.99     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.80/0.99  thf('2', plain,
% 0.80/0.99      (![X9 : $i, X11 : $i]:
% 0.80/0.99         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 0.80/0.99      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.80/0.99  thf('3', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.80/0.99      inference('sup-', [status(thm)], ['1', '2'])).
% 0.80/0.99  thf(t48_xboole_1, axiom,
% 0.80/0.99    (![A:$i,B:$i]:
% 0.80/0.99     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.80/0.99  thf('4', plain,
% 0.80/0.99      (![X19 : $i, X20 : $i]:
% 0.80/0.99         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.80/0.99           = (k3_xboole_0 @ X19 @ X20))),
% 0.80/0.99      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.80/0.99  thf('5', plain,
% 0.80/0.99      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_B_1))),
% 0.80/0.99      inference('sup+', [status(thm)], ['3', '4'])).
% 0.80/0.99  thf(t3_boole, axiom,
% 0.80/0.99    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.80/0.99  thf('6', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.80/0.99      inference('cnf', [status(esa)], [t3_boole])).
% 0.80/0.99  thf('7', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_B_1))),
% 0.80/0.99      inference('demod', [status(thm)], ['5', '6'])).
% 0.80/0.99  thf(commutativity_k3_xboole_0, axiom,
% 0.80/0.99    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.80/0.99  thf('8', plain,
% 0.80/0.99      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.80/0.99      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.80/0.99  thf('9', plain,
% 0.80/0.99      (![X19 : $i, X20 : $i]:
% 0.80/0.99         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.80/0.99           = (k3_xboole_0 @ X19 @ X20))),
% 0.80/0.99      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.80/0.99  thf(commutativity_k2_xboole_0, axiom,
% 0.80/0.99    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.80/0.99  thf('10', plain,
% 0.80/0.99      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.80/0.99      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.80/0.99  thf('11', plain, ((r1_xboole_0 @ sk_B_1 @ sk_C_1)),
% 0.80/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/0.99  thf(t7_xboole_0, axiom,
% 0.80/0.99    (![A:$i]:
% 0.80/0.99     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.80/0.99          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.80/0.99  thf('12', plain,
% 0.80/0.99      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.80/0.99      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.80/0.99  thf(t4_xboole_0, axiom,
% 0.80/0.99    (![A:$i,B:$i]:
% 0.80/0.99     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.80/0.99            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.80/0.99       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.80/0.99            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.80/0.99  thf('13', plain,
% 0.80/0.99      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.80/0.99         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.80/0.99          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.80/0.99      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.80/0.99  thf('14', plain,
% 0.80/0.99      (![X0 : $i, X1 : $i]:
% 0.80/0.99         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.80/0.99      inference('sup-', [status(thm)], ['12', '13'])).
% 0.80/0.99  thf('15', plain, (((k3_xboole_0 @ sk_B_1 @ sk_C_1) = (k1_xboole_0))),
% 0.80/0.99      inference('sup-', [status(thm)], ['11', '14'])).
% 0.80/0.99  thf(t51_xboole_1, axiom,
% 0.80/0.99    (![A:$i,B:$i]:
% 0.80/0.99     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.80/0.99       ( A ) ))).
% 0.80/0.99  thf('16', plain,
% 0.80/0.99      (![X21 : $i, X22 : $i]:
% 0.80/0.99         ((k2_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ (k4_xboole_0 @ X21 @ X22))
% 0.80/0.99           = (X21))),
% 0.80/0.99      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.80/0.99  thf('17', plain,
% 0.80/0.99      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ sk_C_1))
% 0.80/0.99         = (sk_B_1))),
% 0.80/0.99      inference('sup+', [status(thm)], ['15', '16'])).
% 0.80/0.99  thf(t2_boole, axiom,
% 0.80/0.99    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.80/0.99  thf('18', plain,
% 0.80/0.99      (![X12 : $i]: ((k3_xboole_0 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 0.80/0.99      inference('cnf', [status(esa)], [t2_boole])).
% 0.80/0.99  thf('19', plain,
% 0.80/0.99      (![X21 : $i, X22 : $i]:
% 0.80/0.99         ((k2_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ (k4_xboole_0 @ X21 @ X22))
% 0.80/0.99           = (X21))),
% 0.80/0.99      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.80/0.99  thf('20', plain,
% 0.80/0.99      (![X0 : $i]:
% 0.80/0.99         ((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 0.80/0.99      inference('sup+', [status(thm)], ['18', '19'])).
% 0.80/0.99  thf('21', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.80/0.99      inference('cnf', [status(esa)], [t3_boole])).
% 0.80/0.99  thf('22', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.80/0.99      inference('demod', [status(thm)], ['20', '21'])).
% 0.80/0.99  thf('23', plain, (((k4_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_B_1))),
% 0.80/0.99      inference('demod', [status(thm)], ['17', '22'])).
% 0.80/0.99  thf(t41_xboole_1, axiom,
% 0.80/0.99    (![A:$i,B:$i,C:$i]:
% 0.80/0.99     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.80/0.99       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.80/0.99  thf('24', plain,
% 0.80/0.99      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.80/0.99         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.80/0.99           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.80/0.99      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.80/0.99  thf('25', plain,
% 0.80/0.99      (![X0 : $i]:
% 0.80/0.99         ((k4_xboole_0 @ sk_B_1 @ X0)
% 0.80/0.99           = (k4_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ sk_C_1 @ X0)))),
% 0.80/0.99      inference('sup+', [status(thm)], ['23', '24'])).
% 0.80/0.99  thf('26', plain,
% 0.80/0.99      (![X0 : $i]:
% 0.80/0.99         ((k4_xboole_0 @ sk_B_1 @ X0)
% 0.80/0.99           = (k4_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ X0 @ sk_C_1)))),
% 0.80/0.99      inference('sup+', [status(thm)], ['10', '25'])).
% 0.80/0.99  thf('27', plain,
% 0.80/0.99      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.80/0.99         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.80/0.99           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.80/0.99      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.80/0.99  thf('28', plain,
% 0.80/0.99      (![X19 : $i, X20 : $i]:
% 0.80/0.99         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.80/0.99           = (k3_xboole_0 @ X19 @ X20))),
% 0.80/0.99      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.80/0.99  thf('29', plain,
% 0.80/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.80/0.99         ((k4_xboole_0 @ X2 @ 
% 0.80/0.99           (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))
% 0.80/0.99           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.80/0.99      inference('sup+', [status(thm)], ['27', '28'])).
% 0.80/0.99  thf('30', plain,
% 0.80/0.99      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.80/0.99         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.80/0.99           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.80/0.99      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.80/0.99  thf('31', plain,
% 0.80/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.80/0.99         ((k4_xboole_0 @ X2 @ 
% 0.80/0.99           (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))
% 0.80/0.99           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.80/0.99      inference('demod', [status(thm)], ['29', '30'])).
% 0.80/0.99  thf('32', plain,
% 0.80/0.99      (![X0 : $i]:
% 0.80/0.99         ((k4_xboole_0 @ sk_B_1 @ 
% 0.80/0.99           (k2_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B_1 @ X0)))
% 0.80/0.99           = (k3_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ X0) @ sk_C_1))),
% 0.80/0.99      inference('sup+', [status(thm)], ['26', '31'])).
% 0.80/0.99  thf(t39_xboole_1, axiom,
% 0.80/0.99    (![A:$i,B:$i]:
% 0.80/0.99     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.80/0.99  thf('33', plain,
% 0.80/0.99      (![X13 : $i, X14 : $i]:
% 0.80/0.99         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 0.80/0.99           = (k2_xboole_0 @ X13 @ X14))),
% 0.80/0.99      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.80/0.99  thf('34', plain,
% 0.80/0.99      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.80/0.99         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.80/0.99           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.80/0.99      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.80/0.99  thf('35', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.80/0.99      inference('cnf', [status(esa)], [t3_boole])).
% 0.80/0.99  thf('36', plain,
% 0.80/0.99      (![X19 : $i, X20 : $i]:
% 0.80/0.99         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.80/0.99           = (k3_xboole_0 @ X19 @ X20))),
% 0.80/0.99      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.80/0.99  thf('37', plain,
% 0.80/0.99      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.80/0.99      inference('sup+', [status(thm)], ['35', '36'])).
% 0.80/0.99  thf('38', plain,
% 0.80/0.99      (![X12 : $i]: ((k3_xboole_0 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 0.80/0.99      inference('cnf', [status(esa)], [t2_boole])).
% 0.80/0.99  thf('39', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.80/0.99      inference('demod', [status(thm)], ['37', '38'])).
% 0.80/0.99  thf('40', plain,
% 0.80/0.99      (![X0 : $i, X1 : $i]:
% 0.80/0.99         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 0.80/0.99           = (k1_xboole_0))),
% 0.80/0.99      inference('sup+', [status(thm)], ['34', '39'])).
% 0.80/0.99  thf('41', plain,
% 0.80/0.99      (![X13 : $i, X14 : $i]:
% 0.80/0.99         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 0.80/0.99           = (k2_xboole_0 @ X13 @ X14))),
% 0.80/0.99      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.80/0.99  thf('42', plain,
% 0.80/0.99      (![X0 : $i, X1 : $i]:
% 0.80/0.99         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.80/0.99      inference('demod', [status(thm)], ['40', '41'])).
% 0.80/0.99  thf('43', plain,
% 0.80/0.99      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.80/0.99      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.80/0.99  thf('44', plain,
% 0.80/0.99      (![X0 : $i]:
% 0.80/0.99         ((k1_xboole_0) = (k3_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_B_1 @ X0)))),
% 0.80/0.99      inference('demod', [status(thm)], ['32', '33', '42', '43'])).
% 0.80/0.99  thf('45', plain,
% 0.80/0.99      (![X4 : $i, X5 : $i]:
% 0.80/0.99         ((r1_xboole_0 @ X4 @ X5)
% 0.80/0.99          | (r2_hidden @ (sk_C @ X5 @ X4) @ (k3_xboole_0 @ X4 @ X5)))),
% 0.80/0.99      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.80/0.99  thf('46', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.80/0.99      inference('demod', [status(thm)], ['37', '38'])).
% 0.80/0.99  thf('47', plain,
% 0.80/0.99      (![X19 : $i, X20 : $i]:
% 0.80/0.99         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.80/0.99           = (k3_xboole_0 @ X19 @ X20))),
% 0.80/0.99      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.80/0.99  thf('48', plain,
% 0.80/0.99      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.80/0.99      inference('sup+', [status(thm)], ['46', '47'])).
% 0.80/0.99  thf('49', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.80/0.99      inference('cnf', [status(esa)], [t3_boole])).
% 0.80/0.99  thf('50', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.80/0.99      inference('demod', [status(thm)], ['48', '49'])).
% 0.80/0.99  thf('51', plain,
% 0.80/0.99      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.80/0.99         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.80/0.99          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.80/0.99      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.80/0.99  thf('52', plain,
% 0.80/0.99      (![X0 : $i, X1 : $i]:
% 0.80/0.99         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.80/0.99      inference('sup-', [status(thm)], ['50', '51'])).
% 0.80/0.99  thf('53', plain,
% 0.80/0.99      (![X0 : $i, X1 : $i]:
% 0.80/0.99         ((r1_xboole_0 @ X1 @ X0)
% 0.80/0.99          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.80/0.99      inference('sup-', [status(thm)], ['45', '52'])).
% 0.80/0.99  thf('54', plain,
% 0.80/0.99      (![X0 : $i]:
% 0.80/0.99         (~ (r1_xboole_0 @ 
% 0.80/0.99             (k3_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_B_1 @ X0)) @ k1_xboole_0)
% 0.80/0.99          | (r1_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_B_1 @ X0)))),
% 0.80/0.99      inference('sup-', [status(thm)], ['44', '53'])).
% 0.80/0.99  thf('55', plain,
% 0.80/0.99      (![X0 : $i]:
% 0.80/0.99         ((k1_xboole_0) = (k3_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_B_1 @ X0)))),
% 0.80/0.99      inference('demod', [status(thm)], ['32', '33', '42', '43'])).
% 0.80/0.99  thf('56', plain,
% 0.80/0.99      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.80/0.99      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.80/0.99  thf('57', plain,
% 0.80/0.99      (![X12 : $i]: ((k3_xboole_0 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 0.80/0.99      inference('cnf', [status(esa)], [t2_boole])).
% 0.80/0.99  thf('58', plain,
% 0.80/0.99      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.80/0.99      inference('sup+', [status(thm)], ['56', '57'])).
% 0.80/0.99  thf('59', plain,
% 0.80/0.99      (![X0 : $i, X1 : $i]:
% 0.80/0.99         ((r1_xboole_0 @ X1 @ X0)
% 0.80/0.99          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.80/0.99      inference('sup-', [status(thm)], ['45', '52'])).
% 0.80/0.99  thf('60', plain,
% 0.80/0.99      (![X0 : $i]:
% 0.80/0.99         (~ (r1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.80/0.99          | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.80/0.99      inference('sup-', [status(thm)], ['58', '59'])).
% 0.80/0.99  thf('61', plain,
% 0.80/0.99      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.80/0.99      inference('sup+', [status(thm)], ['56', '57'])).
% 0.80/0.99  thf('62', plain,
% 0.80/0.99      (![X0 : $i]:
% 0.80/0.99         (~ (r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.80/0.99          | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.80/0.99      inference('demod', [status(thm)], ['60', '61'])).
% 0.80/0.99  thf('63', plain,
% 0.80/0.99      (![X12 : $i]: ((k3_xboole_0 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 0.80/0.99      inference('cnf', [status(esa)], [t2_boole])).
% 0.80/0.99  thf('64', plain,
% 0.80/0.99      (![X4 : $i, X5 : $i]:
% 0.80/0.99         ((r1_xboole_0 @ X4 @ X5)
% 0.80/0.99          | (r2_hidden @ (sk_C @ X5 @ X4) @ (k3_xboole_0 @ X4 @ X5)))),
% 0.80/0.99      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.80/0.99  thf('65', plain,
% 0.80/0.99      (![X0 : $i]:
% 0.80/0.99         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.80/0.99          | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.80/0.99      inference('sup+', [status(thm)], ['63', '64'])).
% 0.80/0.99  thf('66', plain, (((k3_xboole_0 @ sk_B_1 @ sk_C_1) = (k1_xboole_0))),
% 0.80/0.99      inference('sup-', [status(thm)], ['11', '14'])).
% 0.80/0.99  thf('67', plain,
% 0.80/0.99      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.80/0.99         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.80/0.99          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.80/0.99      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.80/0.99  thf('68', plain,
% 0.80/0.99      (![X0 : $i]:
% 0.80/0.99         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r1_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.80/0.99      inference('sup-', [status(thm)], ['66', '67'])).
% 0.80/0.99  thf('69', plain, ((r1_xboole_0 @ sk_B_1 @ sk_C_1)),
% 0.80/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/0.99  thf('70', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.80/0.99      inference('demod', [status(thm)], ['68', '69'])).
% 0.80/0.99  thf('71', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.80/0.99      inference('clc', [status(thm)], ['65', '70'])).
% 0.80/0.99  thf('72', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.80/0.99      inference('demod', [status(thm)], ['62', '71'])).
% 0.80/0.99  thf('73', plain,
% 0.80/0.99      (![X0 : $i]: (r1_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_B_1 @ X0))),
% 0.80/0.99      inference('demod', [status(thm)], ['54', '55', '72'])).
% 0.80/0.99  thf('74', plain,
% 0.80/0.99      (![X0 : $i]: (r1_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ sk_B_1 @ X0))),
% 0.80/0.99      inference('sup+', [status(thm)], ['9', '73'])).
% 0.80/0.99  thf('75', plain,
% 0.80/0.99      (![X0 : $i]: (r1_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ X0 @ sk_B_1))),
% 0.80/0.99      inference('sup+', [status(thm)], ['8', '74'])).
% 0.80/0.99  thf('76', plain, ((r1_xboole_0 @ sk_C_1 @ sk_A)),
% 0.80/0.99      inference('sup+', [status(thm)], ['7', '75'])).
% 0.80/0.99  thf('77', plain,
% 0.80/0.99      (![X4 : $i, X5 : $i]:
% 0.80/0.99         ((r1_xboole_0 @ X4 @ X5)
% 0.80/0.99          | (r2_hidden @ (sk_C @ X5 @ X4) @ (k3_xboole_0 @ X4 @ X5)))),
% 0.80/0.99      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.80/0.99  thf('78', plain,
% 0.80/0.99      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.80/0.99      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.80/0.99  thf('79', plain,
% 0.80/0.99      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.80/0.99         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.80/0.99          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.80/0.99      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.80/0.99  thf('80', plain,
% 0.80/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.80/0.99         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.80/0.99          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.80/0.99      inference('sup-', [status(thm)], ['78', '79'])).
% 0.80/0.99  thf('81', plain,
% 0.80/0.99      (![X0 : $i, X1 : $i]:
% 0.80/0.99         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.80/0.99      inference('sup-', [status(thm)], ['77', '80'])).
% 0.80/0.99  thf('82', plain, ((r1_xboole_0 @ sk_A @ sk_C_1)),
% 0.80/0.99      inference('sup-', [status(thm)], ['76', '81'])).
% 0.80/0.99  thf('83', plain, ($false), inference('demod', [status(thm)], ['0', '82'])).
% 0.80/0.99  
% 0.80/0.99  % SZS output end Refutation
% 0.80/0.99  
% 0.80/1.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
