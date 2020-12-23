%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7FtmsYiVP2

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:21 EST 2020

% Result     : Theorem 6.51s
% Output     : Refutation 6.51s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 398 expanded)
%              Number of leaves         :   22 ( 134 expanded)
%              Depth                    :   26
%              Number of atoms          :  807 (2992 expanded)
%              Number of equality atoms :   52 ( 196 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X7 ) @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('2',plain,(
    r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('6',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('12',plain,(
    r1_tarski @ k1_xboole_0 @ sk_A ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('14',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('15',plain,(
    ! [X24: $i,X25: $i,X27: $i] :
      ( ( r1_xboole_0 @ X24 @ X25 )
      | ~ ( r1_xboole_0 @ X24 @ ( k2_xboole_0 @ X25 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_A )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    r1_tarski @ k1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('23',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X21 @ X22 )
      | ~ ( r1_xboole_0 @ X22 @ X23 )
      | ( r1_xboole_0 @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','24'])).

thf('26',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('27',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X24: $i,X25: $i,X27: $i] :
      ( ( r1_xboole_0 @ X24 @ X25 )
      | ~ ( r1_xboole_0 @ X24 @ ( k2_xboole_0 @ X25 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('34',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('35',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','40'])).

thf('42',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('45',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ X7 @ X10 ) )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('49',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('50',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X21 @ X22 )
      | ~ ( r1_xboole_0 @ X22 @ X23 )
      | ( r1_xboole_0 @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X1 ) @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['47','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['1','53'])).

thf('55',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('58',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('59',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['56','61'])).

thf('63',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('64',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('65',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ),
    inference(simplify,[status(thm)],['8'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t26_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('68',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_tarski @ ( k3_xboole_0 @ X15 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t26_xboole_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X21 @ X22 )
      | ~ ( r1_xboole_0 @ X22 @ X23 )
      | ( r1_xboole_0 @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) @ X3 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['66','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ X0 @ sk_B ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    r1_tarski @ sk_A @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_tarski @ ( k3_xboole_0 @ X15 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t26_xboole_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k3_xboole_0 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X21 @ X22 )
      | ~ ( r1_xboole_0 @ X22 @ X23 )
      | ( r1_xboole_0 @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ X1 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['74','79'])).

thf('81',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ sk_A ),
    inference('sup+',[status(thm)],['65','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('83',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('85',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X24: $i,X25: $i,X27: $i] :
      ( ( r1_xboole_0 @ X24 @ X25 )
      | ~ ( r1_xboole_0 @ X24 @ ( k2_xboole_0 @ X25 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','88'])).

thf('90',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('93',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('95',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    $false ),
    inference(demod,[status(thm)],['0','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7FtmsYiVP2
% 0.15/0.34  % Computer   : n014.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 09:19:52 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.34  % Running portfolio for 600 s
% 0.15/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 6.51/6.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.51/6.68  % Solved by: fo/fo7.sh
% 6.51/6.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.51/6.68  % done 12265 iterations in 6.225s
% 6.51/6.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.51/6.68  % SZS output start Refutation
% 6.51/6.68  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 6.51/6.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.51/6.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.51/6.68  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 6.51/6.68  thf(sk_A_type, type, sk_A: $i).
% 6.51/6.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 6.51/6.68  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 6.51/6.68  thf(sk_B_type, type, sk_B: $i).
% 6.51/6.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 6.51/6.68  thf(sk_C_1_type, type, sk_C_1: $i).
% 6.51/6.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.51/6.68  thf(t77_xboole_1, conjecture,
% 6.51/6.68    (![A:$i,B:$i,C:$i]:
% 6.51/6.68     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 6.51/6.68          ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 6.51/6.68  thf(zf_stmt_0, negated_conjecture,
% 6.51/6.68    (~( ![A:$i,B:$i,C:$i]:
% 6.51/6.68        ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 6.51/6.68             ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )),
% 6.51/6.68    inference('cnf.neg', [status(esa)], [t77_xboole_1])).
% 6.51/6.68  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 6.51/6.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.51/6.68  thf(t4_xboole_0, axiom,
% 6.51/6.68    (![A:$i,B:$i]:
% 6.51/6.68     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 6.51/6.68            ( r1_xboole_0 @ A @ B ) ) ) & 
% 6.51/6.68       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 6.51/6.68            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 6.51/6.68  thf('1', plain,
% 6.51/6.68      (![X7 : $i, X8 : $i]:
% 6.51/6.68         ((r1_xboole_0 @ X7 @ X8)
% 6.51/6.68          | (r2_hidden @ (sk_C @ X8 @ X7) @ (k3_xboole_0 @ X7 @ X8)))),
% 6.51/6.68      inference('cnf', [status(esa)], [t4_xboole_0])).
% 6.51/6.68  thf('2', plain, ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1))),
% 6.51/6.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.51/6.68  thf(d7_xboole_0, axiom,
% 6.51/6.68    (![A:$i,B:$i]:
% 6.51/6.68     ( ( r1_xboole_0 @ A @ B ) <=>
% 6.51/6.68       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 6.51/6.68  thf('3', plain,
% 6.51/6.68      (![X2 : $i, X3 : $i]:
% 6.51/6.68         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 6.51/6.68      inference('cnf', [status(esa)], [d7_xboole_0])).
% 6.51/6.68  thf('4', plain,
% 6.51/6.68      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1)) = (k1_xboole_0))),
% 6.51/6.68      inference('sup-', [status(thm)], ['2', '3'])).
% 6.51/6.68  thf(commutativity_k3_xboole_0, axiom,
% 6.51/6.68    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 6.51/6.68  thf('5', plain,
% 6.51/6.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 6.51/6.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 6.51/6.68  thf('6', plain,
% 6.51/6.68      (![X2 : $i, X4 : $i]:
% 6.51/6.68         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 6.51/6.68      inference('cnf', [status(esa)], [d7_xboole_0])).
% 6.51/6.68  thf('7', plain,
% 6.51/6.68      (![X0 : $i, X1 : $i]:
% 6.51/6.68         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 6.51/6.68      inference('sup-', [status(thm)], ['5', '6'])).
% 6.51/6.68  thf('8', plain,
% 6.51/6.68      ((((k1_xboole_0) != (k1_xboole_0))
% 6.51/6.68        | (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C_1) @ sk_A))),
% 6.51/6.68      inference('sup-', [status(thm)], ['4', '7'])).
% 6.51/6.68  thf('9', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C_1) @ sk_A)),
% 6.51/6.68      inference('simplify', [status(thm)], ['8'])).
% 6.51/6.68  thf('10', plain,
% 6.51/6.68      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1)) = (k1_xboole_0))),
% 6.51/6.68      inference('sup-', [status(thm)], ['2', '3'])).
% 6.51/6.68  thf(t17_xboole_1, axiom,
% 6.51/6.68    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 6.51/6.68  thf('11', plain,
% 6.51/6.68      (![X13 : $i, X14 : $i]: (r1_tarski @ (k3_xboole_0 @ X13 @ X14) @ X13)),
% 6.51/6.68      inference('cnf', [status(esa)], [t17_xboole_1])).
% 6.51/6.68  thf('12', plain, ((r1_tarski @ k1_xboole_0 @ sk_A)),
% 6.51/6.68      inference('sup+', [status(thm)], ['10', '11'])).
% 6.51/6.68  thf(t12_xboole_1, axiom,
% 6.51/6.68    (![A:$i,B:$i]:
% 6.51/6.68     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 6.51/6.68  thf('13', plain,
% 6.51/6.68      (![X11 : $i, X12 : $i]:
% 6.51/6.68         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 6.51/6.68      inference('cnf', [status(esa)], [t12_xboole_1])).
% 6.51/6.68  thf('14', plain, (((k2_xboole_0 @ k1_xboole_0 @ sk_A) = (sk_A))),
% 6.51/6.68      inference('sup-', [status(thm)], ['12', '13'])).
% 6.51/6.68  thf(t70_xboole_1, axiom,
% 6.51/6.68    (![A:$i,B:$i,C:$i]:
% 6.51/6.68     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 6.51/6.68            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 6.51/6.68       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 6.51/6.68            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 6.51/6.68  thf('15', plain,
% 6.51/6.68      (![X24 : $i, X25 : $i, X27 : $i]:
% 6.51/6.68         ((r1_xboole_0 @ X24 @ X25)
% 6.51/6.68          | ~ (r1_xboole_0 @ X24 @ (k2_xboole_0 @ X25 @ X27)))),
% 6.51/6.68      inference('cnf', [status(esa)], [t70_xboole_1])).
% 6.51/6.68  thf('16', plain,
% 6.51/6.68      (![X0 : $i]:
% 6.51/6.68         (~ (r1_xboole_0 @ X0 @ sk_A) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 6.51/6.68      inference('sup-', [status(thm)], ['14', '15'])).
% 6.51/6.68  thf('17', plain,
% 6.51/6.68      ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C_1) @ k1_xboole_0)),
% 6.51/6.68      inference('sup-', [status(thm)], ['9', '16'])).
% 6.51/6.68  thf('18', plain,
% 6.51/6.68      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1)) = (k1_xboole_0))),
% 6.51/6.68      inference('sup-', [status(thm)], ['2', '3'])).
% 6.51/6.68  thf('19', plain,
% 6.51/6.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 6.51/6.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 6.51/6.68  thf('20', plain,
% 6.51/6.68      (![X13 : $i, X14 : $i]: (r1_tarski @ (k3_xboole_0 @ X13 @ X14) @ X13)),
% 6.51/6.68      inference('cnf', [status(esa)], [t17_xboole_1])).
% 6.51/6.68  thf('21', plain,
% 6.51/6.68      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 6.51/6.68      inference('sup+', [status(thm)], ['19', '20'])).
% 6.51/6.68  thf('22', plain, ((r1_tarski @ k1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C_1))),
% 6.51/6.68      inference('sup+', [status(thm)], ['18', '21'])).
% 6.51/6.68  thf(t63_xboole_1, axiom,
% 6.51/6.68    (![A:$i,B:$i,C:$i]:
% 6.51/6.68     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 6.51/6.68       ( r1_xboole_0 @ A @ C ) ))).
% 6.51/6.68  thf('23', plain,
% 6.51/6.68      (![X21 : $i, X22 : $i, X23 : $i]:
% 6.51/6.68         (~ (r1_tarski @ X21 @ X22)
% 6.51/6.68          | ~ (r1_xboole_0 @ X22 @ X23)
% 6.51/6.68          | (r1_xboole_0 @ X21 @ X23))),
% 6.51/6.68      inference('cnf', [status(esa)], [t63_xboole_1])).
% 6.51/6.68  thf('24', plain,
% 6.51/6.68      (![X0 : $i]:
% 6.51/6.68         ((r1_xboole_0 @ k1_xboole_0 @ X0)
% 6.51/6.68          | ~ (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C_1) @ X0))),
% 6.51/6.68      inference('sup-', [status(thm)], ['22', '23'])).
% 6.51/6.68  thf('25', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 6.51/6.68      inference('sup-', [status(thm)], ['17', '24'])).
% 6.51/6.68  thf('26', plain,
% 6.51/6.68      (![X13 : $i, X14 : $i]: (r1_tarski @ (k3_xboole_0 @ X13 @ X14) @ X13)),
% 6.51/6.68      inference('cnf', [status(esa)], [t17_xboole_1])).
% 6.51/6.68  thf('27', plain,
% 6.51/6.68      (![X11 : $i, X12 : $i]:
% 6.51/6.68         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 6.51/6.68      inference('cnf', [status(esa)], [t12_xboole_1])).
% 6.51/6.68  thf('28', plain,
% 6.51/6.68      (![X0 : $i, X1 : $i]:
% 6.51/6.68         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 6.51/6.68      inference('sup-', [status(thm)], ['26', '27'])).
% 6.51/6.68  thf('29', plain,
% 6.51/6.68      (![X24 : $i, X25 : $i, X27 : $i]:
% 6.51/6.68         ((r1_xboole_0 @ X24 @ X25)
% 6.51/6.68          | ~ (r1_xboole_0 @ X24 @ (k2_xboole_0 @ X25 @ X27)))),
% 6.51/6.68      inference('cnf', [status(esa)], [t70_xboole_1])).
% 6.51/6.68  thf('30', plain,
% 6.51/6.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.51/6.68         (~ (r1_xboole_0 @ X2 @ X0)
% 6.51/6.68          | (r1_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 6.51/6.68      inference('sup-', [status(thm)], ['28', '29'])).
% 6.51/6.68  thf('31', plain,
% 6.51/6.68      (![X0 : $i]:
% 6.51/6.68         (r1_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 6.51/6.68      inference('sup-', [status(thm)], ['25', '30'])).
% 6.51/6.68  thf('32', plain,
% 6.51/6.68      (![X2 : $i, X3 : $i]:
% 6.51/6.68         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 6.51/6.68      inference('cnf', [status(esa)], [d7_xboole_0])).
% 6.51/6.68  thf('33', plain,
% 6.51/6.68      (![X0 : $i]:
% 6.51/6.68         ((k3_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0))
% 6.51/6.68           = (k1_xboole_0))),
% 6.51/6.68      inference('sup-', [status(thm)], ['31', '32'])).
% 6.51/6.68  thf(t3_boole, axiom,
% 6.51/6.68    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 6.51/6.68  thf('34', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 6.51/6.68      inference('cnf', [status(esa)], [t3_boole])).
% 6.51/6.68  thf(t48_xboole_1, axiom,
% 6.51/6.68    (![A:$i,B:$i]:
% 6.51/6.68     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 6.51/6.68  thf('35', plain,
% 6.51/6.68      (![X19 : $i, X20 : $i]:
% 6.51/6.68         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 6.51/6.68           = (k3_xboole_0 @ X19 @ X20))),
% 6.51/6.68      inference('cnf', [status(esa)], [t48_xboole_1])).
% 6.51/6.68  thf('36', plain,
% 6.51/6.68      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 6.51/6.68      inference('sup+', [status(thm)], ['34', '35'])).
% 6.51/6.68  thf('37', plain,
% 6.51/6.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 6.51/6.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 6.51/6.68  thf('38', plain,
% 6.51/6.68      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 6.51/6.68      inference('sup+', [status(thm)], ['36', '37'])).
% 6.51/6.68  thf('39', plain,
% 6.51/6.68      (![X19 : $i, X20 : $i]:
% 6.51/6.68         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 6.51/6.68           = (k3_xboole_0 @ X19 @ X20))),
% 6.51/6.68      inference('cnf', [status(esa)], [t48_xboole_1])).
% 6.51/6.68  thf('40', plain,
% 6.51/6.68      (![X0 : $i]:
% 6.51/6.68         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X0))
% 6.51/6.68           = (k3_xboole_0 @ X0 @ X0))),
% 6.51/6.68      inference('sup+', [status(thm)], ['38', '39'])).
% 6.51/6.68  thf('41', plain,
% 6.51/6.68      (![X0 : $i]:
% 6.51/6.68         ((k4_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 6.51/6.68           = (k3_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0) @ 
% 6.51/6.68              (k3_xboole_0 @ k1_xboole_0 @ X0)))),
% 6.51/6.68      inference('sup+', [status(thm)], ['33', '40'])).
% 6.51/6.68  thf('42', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 6.51/6.68      inference('cnf', [status(esa)], [t3_boole])).
% 6.51/6.68  thf('43', plain,
% 6.51/6.68      (![X0 : $i]:
% 6.51/6.68         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 6.51/6.68           = (k3_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0) @ 
% 6.51/6.68              (k3_xboole_0 @ k1_xboole_0 @ X0)))),
% 6.51/6.68      inference('demod', [status(thm)], ['41', '42'])).
% 6.51/6.68  thf('44', plain,
% 6.51/6.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 6.51/6.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 6.51/6.68  thf('45', plain,
% 6.51/6.68      (![X7 : $i, X9 : $i, X10 : $i]:
% 6.51/6.68         (~ (r2_hidden @ X9 @ (k3_xboole_0 @ X7 @ X10))
% 6.51/6.68          | ~ (r1_xboole_0 @ X7 @ X10))),
% 6.51/6.68      inference('cnf', [status(esa)], [t4_xboole_0])).
% 6.51/6.68  thf('46', plain,
% 6.51/6.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.51/6.68         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 6.51/6.68          | ~ (r1_xboole_0 @ X0 @ X1))),
% 6.51/6.68      inference('sup-', [status(thm)], ['44', '45'])).
% 6.51/6.68  thf('47', plain,
% 6.51/6.68      (![X0 : $i, X1 : $i]:
% 6.51/6.68         (~ (r2_hidden @ X1 @ (k3_xboole_0 @ k1_xboole_0 @ X0))
% 6.51/6.68          | ~ (r1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0) @ 
% 6.51/6.68               (k3_xboole_0 @ k1_xboole_0 @ X0)))),
% 6.51/6.68      inference('sup-', [status(thm)], ['43', '46'])).
% 6.51/6.68  thf('48', plain,
% 6.51/6.68      (![X0 : $i]:
% 6.51/6.68         (r1_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 6.51/6.68      inference('sup-', [status(thm)], ['25', '30'])).
% 6.51/6.68  thf('49', plain,
% 6.51/6.68      (![X13 : $i, X14 : $i]: (r1_tarski @ (k3_xboole_0 @ X13 @ X14) @ X13)),
% 6.51/6.68      inference('cnf', [status(esa)], [t17_xboole_1])).
% 6.51/6.68  thf('50', plain,
% 6.51/6.68      (![X21 : $i, X22 : $i, X23 : $i]:
% 6.51/6.68         (~ (r1_tarski @ X21 @ X22)
% 6.51/6.68          | ~ (r1_xboole_0 @ X22 @ X23)
% 6.51/6.68          | (r1_xboole_0 @ X21 @ X23))),
% 6.51/6.68      inference('cnf', [status(esa)], [t63_xboole_1])).
% 6.51/6.68  thf('51', plain,
% 6.51/6.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.51/6.68         ((r1_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2)
% 6.51/6.68          | ~ (r1_xboole_0 @ X0 @ X2))),
% 6.51/6.68      inference('sup-', [status(thm)], ['49', '50'])).
% 6.51/6.68  thf('52', plain,
% 6.51/6.68      (![X0 : $i, X1 : $i]:
% 6.51/6.68         (r1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X1) @ 
% 6.51/6.68          (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 6.51/6.68      inference('sup-', [status(thm)], ['48', '51'])).
% 6.51/6.68  thf('53', plain,
% 6.51/6.68      (![X0 : $i, X1 : $i]:
% 6.51/6.68         ~ (r2_hidden @ X1 @ (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 6.51/6.68      inference('demod', [status(thm)], ['47', '52'])).
% 6.51/6.68  thf('54', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 6.51/6.68      inference('sup-', [status(thm)], ['1', '53'])).
% 6.51/6.68  thf('55', plain,
% 6.51/6.68      (![X2 : $i, X3 : $i]:
% 6.51/6.68         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 6.51/6.68      inference('cnf', [status(esa)], [d7_xboole_0])).
% 6.51/6.68  thf('56', plain,
% 6.51/6.68      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 6.51/6.68      inference('sup-', [status(thm)], ['54', '55'])).
% 6.51/6.68  thf('57', plain,
% 6.51/6.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 6.51/6.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 6.51/6.68  thf('58', plain,
% 6.51/6.68      (![X19 : $i, X20 : $i]:
% 6.51/6.68         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 6.51/6.68           = (k3_xboole_0 @ X19 @ X20))),
% 6.51/6.68      inference('cnf', [status(esa)], [t48_xboole_1])).
% 6.51/6.68  thf('59', plain,
% 6.51/6.68      (![X19 : $i, X20 : $i]:
% 6.51/6.68         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 6.51/6.68           = (k3_xboole_0 @ X19 @ X20))),
% 6.51/6.68      inference('cnf', [status(esa)], [t48_xboole_1])).
% 6.51/6.68  thf('60', plain,
% 6.51/6.68      (![X0 : $i, X1 : $i]:
% 6.51/6.68         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 6.51/6.68           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 6.51/6.68      inference('sup+', [status(thm)], ['58', '59'])).
% 6.51/6.68  thf('61', plain,
% 6.51/6.68      (![X0 : $i, X1 : $i]:
% 6.51/6.68         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 6.51/6.68           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 6.51/6.68      inference('sup+', [status(thm)], ['57', '60'])).
% 6.51/6.68  thf('62', plain,
% 6.51/6.68      (![X0 : $i]:
% 6.51/6.68         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 6.51/6.68           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 6.51/6.68      inference('sup+', [status(thm)], ['56', '61'])).
% 6.51/6.68  thf('63', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 6.51/6.68      inference('cnf', [status(esa)], [t3_boole])).
% 6.51/6.68  thf('64', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 6.51/6.68      inference('cnf', [status(esa)], [t3_boole])).
% 6.51/6.68  thf('65', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 6.51/6.68      inference('demod', [status(thm)], ['62', '63', '64'])).
% 6.51/6.68  thf('66', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C_1) @ sk_A)),
% 6.51/6.68      inference('simplify', [status(thm)], ['8'])).
% 6.51/6.68  thf('67', plain,
% 6.51/6.68      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 6.51/6.68      inference('sup+', [status(thm)], ['19', '20'])).
% 6.51/6.68  thf(t26_xboole_1, axiom,
% 6.51/6.68    (![A:$i,B:$i,C:$i]:
% 6.51/6.68     ( ( r1_tarski @ A @ B ) =>
% 6.51/6.68       ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ ( k3_xboole_0 @ B @ C ) ) ))).
% 6.51/6.68  thf('68', plain,
% 6.51/6.68      (![X15 : $i, X16 : $i, X17 : $i]:
% 6.51/6.68         (~ (r1_tarski @ X15 @ X16)
% 6.51/6.68          | (r1_tarski @ (k3_xboole_0 @ X15 @ X17) @ (k3_xboole_0 @ X16 @ X17)))),
% 6.51/6.68      inference('cnf', [status(esa)], [t26_xboole_1])).
% 6.51/6.68  thf('69', plain,
% 6.51/6.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.51/6.68         (r1_tarski @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2) @ 
% 6.51/6.68          (k3_xboole_0 @ X0 @ X2))),
% 6.51/6.68      inference('sup-', [status(thm)], ['67', '68'])).
% 6.51/6.68  thf('70', plain,
% 6.51/6.68      (![X21 : $i, X22 : $i, X23 : $i]:
% 6.51/6.68         (~ (r1_tarski @ X21 @ X22)
% 6.51/6.68          | ~ (r1_xboole_0 @ X22 @ X23)
% 6.51/6.68          | (r1_xboole_0 @ X21 @ X23))),
% 6.51/6.68      inference('cnf', [status(esa)], [t63_xboole_1])).
% 6.51/6.68  thf('71', plain,
% 6.51/6.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.51/6.68         ((r1_xboole_0 @ (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0) @ X3)
% 6.51/6.68          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X3))),
% 6.51/6.68      inference('sup-', [status(thm)], ['69', '70'])).
% 6.51/6.68  thf('72', plain,
% 6.51/6.68      (![X0 : $i]:
% 6.51/6.68         (r1_xboole_0 @ (k3_xboole_0 @ (k3_xboole_0 @ X0 @ sk_B) @ sk_C_1) @ 
% 6.51/6.68          sk_A)),
% 6.51/6.68      inference('sup-', [status(thm)], ['66', '71'])).
% 6.51/6.68  thf('73', plain,
% 6.51/6.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 6.51/6.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 6.51/6.68  thf('74', plain,
% 6.51/6.68      (![X0 : $i]:
% 6.51/6.68         (r1_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ X0 @ sk_B)) @ 
% 6.51/6.68          sk_A)),
% 6.51/6.68      inference('demod', [status(thm)], ['72', '73'])).
% 6.51/6.68  thf('75', plain, ((r1_tarski @ sk_A @ sk_C_1)),
% 6.51/6.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.51/6.68  thf('76', plain,
% 6.51/6.68      (![X15 : $i, X16 : $i, X17 : $i]:
% 6.51/6.68         (~ (r1_tarski @ X15 @ X16)
% 6.51/6.68          | (r1_tarski @ (k3_xboole_0 @ X15 @ X17) @ (k3_xboole_0 @ X16 @ X17)))),
% 6.51/6.68      inference('cnf', [status(esa)], [t26_xboole_1])).
% 6.51/6.68  thf('77', plain,
% 6.51/6.68      (![X0 : $i]:
% 6.51/6.68         (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ (k3_xboole_0 @ sk_C_1 @ X0))),
% 6.51/6.68      inference('sup-', [status(thm)], ['75', '76'])).
% 6.51/6.68  thf('78', plain,
% 6.51/6.68      (![X21 : $i, X22 : $i, X23 : $i]:
% 6.51/6.68         (~ (r1_tarski @ X21 @ X22)
% 6.51/6.68          | ~ (r1_xboole_0 @ X22 @ X23)
% 6.51/6.68          | (r1_xboole_0 @ X21 @ X23))),
% 6.51/6.68      inference('cnf', [status(esa)], [t63_xboole_1])).
% 6.51/6.68  thf('79', plain,
% 6.51/6.68      (![X0 : $i, X1 : $i]:
% 6.51/6.68         ((r1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ X1)
% 6.51/6.68          | ~ (r1_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ X0) @ X1))),
% 6.51/6.68      inference('sup-', [status(thm)], ['77', '78'])).
% 6.51/6.68  thf('80', plain,
% 6.51/6.68      (![X0 : $i]:
% 6.51/6.68         (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)) @ sk_A)),
% 6.51/6.68      inference('sup-', [status(thm)], ['74', '79'])).
% 6.51/6.68  thf('81', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ sk_A)),
% 6.51/6.68      inference('sup+', [status(thm)], ['65', '80'])).
% 6.51/6.68  thf('82', plain,
% 6.51/6.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 6.51/6.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 6.51/6.68  thf('83', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_A)),
% 6.51/6.68      inference('demod', [status(thm)], ['81', '82'])).
% 6.51/6.68  thf('84', plain,
% 6.51/6.68      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 6.51/6.68      inference('sup+', [status(thm)], ['19', '20'])).
% 6.51/6.68  thf('85', plain,
% 6.51/6.68      (![X11 : $i, X12 : $i]:
% 6.51/6.68         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 6.51/6.68      inference('cnf', [status(esa)], [t12_xboole_1])).
% 6.51/6.68  thf('86', plain,
% 6.51/6.68      (![X0 : $i, X1 : $i]:
% 6.51/6.68         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 6.51/6.68      inference('sup-', [status(thm)], ['84', '85'])).
% 6.51/6.68  thf('87', plain,
% 6.51/6.68      (![X24 : $i, X25 : $i, X27 : $i]:
% 6.51/6.68         ((r1_xboole_0 @ X24 @ X25)
% 6.51/6.68          | ~ (r1_xboole_0 @ X24 @ (k2_xboole_0 @ X25 @ X27)))),
% 6.51/6.68      inference('cnf', [status(esa)], [t70_xboole_1])).
% 6.51/6.68  thf('88', plain,
% 6.51/6.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.51/6.68         (~ (r1_xboole_0 @ X2 @ X0)
% 6.51/6.68          | (r1_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 6.51/6.68      inference('sup-', [status(thm)], ['86', '87'])).
% 6.51/6.68  thf('89', plain,
% 6.51/6.68      (![X0 : $i]:
% 6.51/6.68         (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ (k3_xboole_0 @ X0 @ sk_A))),
% 6.51/6.68      inference('sup-', [status(thm)], ['83', '88'])).
% 6.51/6.68  thf('90', plain,
% 6.51/6.68      (![X2 : $i, X3 : $i]:
% 6.51/6.68         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 6.51/6.68      inference('cnf', [status(esa)], [d7_xboole_0])).
% 6.51/6.68  thf('91', plain,
% 6.51/6.68      (![X0 : $i]:
% 6.51/6.68         ((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ 
% 6.51/6.68           (k3_xboole_0 @ X0 @ sk_A)) = (k1_xboole_0))),
% 6.51/6.68      inference('sup-', [status(thm)], ['89', '90'])).
% 6.51/6.68  thf('92', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 6.51/6.68      inference('demod', [status(thm)], ['62', '63', '64'])).
% 6.51/6.68  thf('93', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 6.51/6.68      inference('sup+', [status(thm)], ['91', '92'])).
% 6.51/6.68  thf('94', plain,
% 6.51/6.68      (![X0 : $i, X1 : $i]:
% 6.51/6.68         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 6.51/6.68      inference('sup-', [status(thm)], ['5', '6'])).
% 6.51/6.68  thf('95', plain,
% 6.51/6.68      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_B))),
% 6.51/6.68      inference('sup-', [status(thm)], ['93', '94'])).
% 6.51/6.68  thf('96', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 6.51/6.68      inference('simplify', [status(thm)], ['95'])).
% 6.51/6.68  thf('97', plain, ($false), inference('demod', [status(thm)], ['0', '96'])).
% 6.51/6.68  
% 6.51/6.68  % SZS output end Refutation
% 6.51/6.68  
% 6.51/6.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
