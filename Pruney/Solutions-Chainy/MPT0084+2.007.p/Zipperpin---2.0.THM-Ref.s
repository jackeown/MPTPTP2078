%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uqOUagv4Ht

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:19 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 168 expanded)
%              Number of leaves         :   26 (  65 expanded)
%              Depth                    :   12
%              Number of atoms          :  673 (1333 expanded)
%              Number of equality atoms :   60 ( 124 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ~ ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('2',plain,(
    r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('3',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('4',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('8',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('9',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('10',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t50_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('11',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k3_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ ( k3_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t50_xboole_1])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('12',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('13',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k3_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ ( k3_xboole_0 @ X21 @ X23 ) ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) )
    = ( k3_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    r1_tarski @ sk_A @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('17',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('18',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('19',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['14','17','18'])).

thf('20',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('28',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('30',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k3_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ ( k3_xboole_0 @ X21 @ X23 ) ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('35',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ k1_xboole_0 ) @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['19','41'])).

thf('43',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('44',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X24 @ X25 ) @ ( k4_xboole_0 @ X24 @ X25 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('45',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('46',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['44','49'])).

thf('51',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('52',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X24 @ X25 ) @ ( k4_xboole_0 @ X24 @ X25 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','55'])).

thf('57',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('59',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','55'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('64',plain,(
    ! [X29: $i] :
      ( r1_xboole_0 @ X29 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['42','43','65'])).

thf('67',plain,(
    r1_xboole_0 @ sk_A @ sk_B_1 ),
    inference('sup-',[status(thm)],['1','66'])).

thf('68',plain,(
    $false ),
    inference(demod,[status(thm)],['0','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uqOUagv4Ht
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:09:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.45/0.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.64  % Solved by: fo/fo7.sh
% 0.45/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.64  % done 422 iterations in 0.173s
% 0.45/0.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.64  % SZS output start Refutation
% 0.45/0.64  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.64  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.45/0.64  thf(sk_B_type, type, sk_B: $i > $i).
% 0.45/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.64  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.45/0.64  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.45/0.64  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.64  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.64  thf(t77_xboole_1, conjecture,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.45/0.64          ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 0.45/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.64    (~( ![A:$i,B:$i,C:$i]:
% 0.45/0.64        ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.45/0.64             ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )),
% 0.45/0.64    inference('cnf.neg', [status(esa)], [t77_xboole_1])).
% 0.45/0.64  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B_1)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(t4_xboole_0, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.45/0.64            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.45/0.64       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.45/0.64            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.45/0.64  thf('1', plain,
% 0.45/0.64      (![X2 : $i, X3 : $i]:
% 0.45/0.64         ((r1_xboole_0 @ X2 @ X3)
% 0.45/0.64          | (r2_hidden @ (sk_C @ X3 @ X2) @ (k3_xboole_0 @ X2 @ X3)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.45/0.64  thf('2', plain, ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(t7_xboole_0, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.45/0.64          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.45/0.64  thf('3', plain,
% 0.45/0.64      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.45/0.64      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.45/0.64  thf('4', plain,
% 0.45/0.64      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.45/0.64         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.45/0.64          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.45/0.64      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.45/0.64  thf('5', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['3', '4'])).
% 0.45/0.64  thf('6', plain,
% 0.45/0.64      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B_1 @ sk_C_1)) = (k1_xboole_0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['2', '5'])).
% 0.45/0.64  thf(t47_xboole_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.45/0.64  thf('7', plain,
% 0.45/0.64      (![X14 : $i, X15 : $i]:
% 0.45/0.64         ((k4_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15))
% 0.45/0.64           = (k4_xboole_0 @ X14 @ X15))),
% 0.45/0.64      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.45/0.64  thf('8', plain,
% 0.45/0.64      (((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.45/0.64         = (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 0.45/0.64      inference('sup+', [status(thm)], ['6', '7'])).
% 0.45/0.64  thf(t3_boole, axiom,
% 0.45/0.64    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.45/0.64  thf('9', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.45/0.64      inference('cnf', [status(esa)], [t3_boole])).
% 0.45/0.64  thf('10', plain,
% 0.45/0.64      (((sk_A) = (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 0.45/0.64      inference('demod', [status(thm)], ['8', '9'])).
% 0.45/0.64  thf(t50_xboole_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.45/0.64       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.45/0.64  thf('11', plain,
% 0.45/0.64      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.45/0.64         ((k3_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X23))
% 0.45/0.64           = (k4_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ 
% 0.45/0.64              (k3_xboole_0 @ X21 @ X23)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t50_xboole_1])).
% 0.45/0.64  thf(t49_xboole_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.45/0.64       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.45/0.64  thf('12', plain,
% 0.45/0.64      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.45/0.64         ((k3_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 0.45/0.64           = (k4_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X20))),
% 0.45/0.64      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.45/0.64  thf('13', plain,
% 0.45/0.64      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.45/0.64         ((k3_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X23))
% 0.45/0.64           = (k3_xboole_0 @ X21 @ 
% 0.45/0.64              (k4_xboole_0 @ X22 @ (k3_xboole_0 @ X21 @ X23))))),
% 0.45/0.64      inference('demod', [status(thm)], ['11', '12'])).
% 0.45/0.64  thf('14', plain,
% 0.45/0.64      (((k3_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ sk_A @ sk_C_1))
% 0.45/0.64         = (k3_xboole_0 @ sk_B_1 @ sk_A))),
% 0.45/0.64      inference('sup+', [status(thm)], ['10', '13'])).
% 0.45/0.64  thf('15', plain, ((r1_tarski @ sk_A @ sk_C_1)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(l32_xboole_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.64  thf('16', plain,
% 0.45/0.64      (![X7 : $i, X9 : $i]:
% 0.45/0.64         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.45/0.64      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.45/0.64  thf('17', plain, (((k4_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['15', '16'])).
% 0.45/0.64  thf(t2_boole, axiom,
% 0.45/0.64    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.45/0.64  thf('18', plain,
% 0.45/0.64      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.64      inference('cnf', [status(esa)], [t2_boole])).
% 0.45/0.64  thf('19', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_B_1 @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['14', '17', '18'])).
% 0.45/0.64  thf('20', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.45/0.64      inference('cnf', [status(esa)], [t3_boole])).
% 0.45/0.64  thf(t48_xboole_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.45/0.64  thf('21', plain,
% 0.45/0.64      (![X16 : $i, X17 : $i]:
% 0.45/0.64         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.45/0.64           = (k3_xboole_0 @ X16 @ X17))),
% 0.45/0.64      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.64  thf('22', plain,
% 0.45/0.64      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['20', '21'])).
% 0.45/0.64  thf('23', plain,
% 0.45/0.64      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.64      inference('cnf', [status(esa)], [t2_boole])).
% 0.45/0.64  thf('24', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.45/0.64      inference('demod', [status(thm)], ['22', '23'])).
% 0.45/0.64  thf('25', plain,
% 0.45/0.64      (![X16 : $i, X17 : $i]:
% 0.45/0.64         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.45/0.64           = (k3_xboole_0 @ X16 @ X17))),
% 0.45/0.64      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.64  thf('26', plain,
% 0.45/0.64      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['24', '25'])).
% 0.45/0.64  thf('27', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.45/0.64      inference('cnf', [status(esa)], [t3_boole])).
% 0.45/0.64  thf('28', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.45/0.64      inference('demod', [status(thm)], ['26', '27'])).
% 0.45/0.64  thf('29', plain,
% 0.45/0.64      (![X16 : $i, X17 : $i]:
% 0.45/0.64         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.45/0.64           = (k3_xboole_0 @ X16 @ X17))),
% 0.45/0.64      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.64  thf('30', plain,
% 0.45/0.64      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.45/0.64         ((k3_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 0.45/0.64           = (k4_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X20))),
% 0.45/0.64      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.45/0.64  thf('31', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.64         ((k3_xboole_0 @ X2 @ 
% 0.45/0.64           (k4_xboole_0 @ X1 @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)))
% 0.45/0.64           = (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['29', '30'])).
% 0.45/0.64  thf('32', plain,
% 0.45/0.64      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.45/0.64         ((k3_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 0.45/0.64           = (k4_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X20))),
% 0.45/0.64      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.45/0.64  thf('33', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.64         ((k3_xboole_0 @ X2 @ 
% 0.45/0.64           (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))
% 0.45/0.64           = (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 0.45/0.64      inference('demod', [status(thm)], ['31', '32'])).
% 0.45/0.64  thf('34', plain,
% 0.45/0.64      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.45/0.64         ((k3_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X23))
% 0.45/0.64           = (k3_xboole_0 @ X21 @ 
% 0.45/0.64              (k4_xboole_0 @ X22 @ (k3_xboole_0 @ X21 @ X23))))),
% 0.45/0.64      inference('demod', [status(thm)], ['11', '12'])).
% 0.45/0.64  thf('35', plain,
% 0.45/0.64      (![X16 : $i, X17 : $i]:
% 0.45/0.64         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.45/0.64           = (k3_xboole_0 @ X16 @ X17))),
% 0.45/0.64      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.64  thf('36', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.64         ((k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.45/0.64           = (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 0.45/0.64      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.45/0.64  thf('37', plain,
% 0.45/0.64      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.45/0.64         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.45/0.64          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.45/0.64      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.45/0.64  thf('38', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.64         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.45/0.64          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['36', '37'])).
% 0.45/0.64  thf('39', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.64         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.45/0.64          | ~ (r1_xboole_0 @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['28', '38'])).
% 0.45/0.64  thf('40', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.64         ((k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.45/0.64           = (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 0.45/0.64      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.45/0.64  thf('41', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.64         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.45/0.64          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)) @ X0))),
% 0.45/0.64      inference('demod', [status(thm)], ['39', '40'])).
% 0.45/0.64  thf('42', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ k1_xboole_0) @ sk_B_1)
% 0.45/0.64          | ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_A @ sk_B_1)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['19', '41'])).
% 0.45/0.64  thf('43', plain,
% 0.45/0.64      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.64      inference('cnf', [status(esa)], [t2_boole])).
% 0.45/0.64  thf(t51_xboole_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.45/0.64       ( A ) ))).
% 0.45/0.64  thf('44', plain,
% 0.45/0.64      (![X24 : $i, X25 : $i]:
% 0.45/0.64         ((k2_xboole_0 @ (k3_xboole_0 @ X24 @ X25) @ (k4_xboole_0 @ X24 @ X25))
% 0.45/0.64           = (X24))),
% 0.45/0.64      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.45/0.64  thf('45', plain,
% 0.45/0.64      (![X14 : $i, X15 : $i]:
% 0.45/0.64         ((k4_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15))
% 0.45/0.64           = (k4_xboole_0 @ X14 @ X15))),
% 0.45/0.64      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.45/0.64  thf(t39_xboole_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.45/0.64  thf('46', plain,
% 0.45/0.64      (![X11 : $i, X12 : $i]:
% 0.45/0.64         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 0.45/0.64           = (k2_xboole_0 @ X11 @ X12))),
% 0.45/0.64      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.45/0.64  thf('47', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.45/0.64           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 0.45/0.64      inference('sup+', [status(thm)], ['45', '46'])).
% 0.45/0.64  thf(commutativity_k2_xboole_0, axiom,
% 0.45/0.64    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.45/0.64  thf('48', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.45/0.64      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.45/0.64  thf('49', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.45/0.64           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.45/0.64      inference('demod', [status(thm)], ['47', '48'])).
% 0.45/0.64  thf('50', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         ((X0) = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.45/0.64      inference('sup+', [status(thm)], ['44', '49'])).
% 0.45/0.64  thf('51', plain,
% 0.45/0.64      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.64      inference('cnf', [status(esa)], [t2_boole])).
% 0.45/0.64  thf('52', plain,
% 0.45/0.64      (![X24 : $i, X25 : $i]:
% 0.45/0.64         ((k2_xboole_0 @ (k3_xboole_0 @ X24 @ X25) @ (k4_xboole_0 @ X24 @ X25))
% 0.45/0.64           = (X24))),
% 0.45/0.64      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.45/0.64  thf('53', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['51', '52'])).
% 0.45/0.64  thf('54', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.45/0.64      inference('cnf', [status(esa)], [t3_boole])).
% 0.45/0.64  thf('55', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.45/0.64      inference('demod', [status(thm)], ['53', '54'])).
% 0.45/0.64  thf('56', plain,
% 0.45/0.64      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['50', '55'])).
% 0.45/0.64  thf('57', plain,
% 0.45/0.64      (![X2 : $i, X3 : $i]:
% 0.45/0.64         ((r1_xboole_0 @ X2 @ X3)
% 0.45/0.64          | (r2_hidden @ (sk_C @ X3 @ X2) @ (k3_xboole_0 @ X2 @ X3)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.45/0.64  thf('58', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.45/0.64      inference('demod', [status(thm)], ['26', '27'])).
% 0.45/0.64  thf('59', plain,
% 0.45/0.64      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.45/0.64         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.45/0.64          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.45/0.64      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.45/0.64  thf('60', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['58', '59'])).
% 0.45/0.64  thf('61', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         ((r1_xboole_0 @ X1 @ X0)
% 0.45/0.64          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['57', '60'])).
% 0.45/0.64  thf('62', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (r1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.45/0.64          | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['56', '61'])).
% 0.45/0.64  thf('63', plain,
% 0.45/0.64      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['50', '55'])).
% 0.45/0.64  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.45/0.64  thf('64', plain, (![X29 : $i]: (r1_xboole_0 @ X29 @ k1_xboole_0)),
% 0.45/0.64      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.45/0.64  thf('65', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.45/0.64      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.45/0.64  thf('66', plain,
% 0.45/0.64      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_A @ sk_B_1))),
% 0.45/0.64      inference('demod', [status(thm)], ['42', '43', '65'])).
% 0.45/0.64  thf('67', plain, ((r1_xboole_0 @ sk_A @ sk_B_1)),
% 0.45/0.64      inference('sup-', [status(thm)], ['1', '66'])).
% 0.45/0.64  thf('68', plain, ($false), inference('demod', [status(thm)], ['0', '67'])).
% 0.45/0.64  
% 0.45/0.64  % SZS output end Refutation
% 0.45/0.64  
% 0.45/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
