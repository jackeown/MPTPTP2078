%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yullXjLzlN

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:55 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 517 expanded)
%              Number of leaves         :   25 ( 167 expanded)
%              Depth                    :   16
%              Number of atoms          :  935 (3823 expanded)
%              Number of equality atoms :  104 ( 445 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t140_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k2_xboole_0 @ ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t140_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('1',plain,(
    ! [X38: $i,X40: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X38 ) @ X40 )
      | ~ ( r2_hidden @ X38 @ X40 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('2',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k1_tarski @ sk_A ) ),
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

thf('6',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ sk_B ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X10 @ X12 ) @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
    = ( k3_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['11'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('27',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','25','26'])).

thf('28',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('29',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('31',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('32',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','35'])).

thf('37',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['27','36'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('38',plain,(
    ! [X15: $i] :
      ( r1_tarski @ k1_xboole_0 @ X15 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('39',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('45',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k1_tarski @ sk_A )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('49',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X26 @ X27 ) @ ( k3_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('50',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('51',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ X26 @ ( k5_xboole_0 @ X27 @ ( k3_xboole_0 @ X26 @ X27 ) ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k2_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['47','54'])).

thf('56',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('57',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('58',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('59',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('61',plain,
    ( ( k2_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['55','56','59','60'])).

thf('62',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('63',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,
    ( k1_xboole_0
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('68',plain,
    ( k1_xboole_0
    = ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('70',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['71','76'])).

thf('78',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['68','77'])).

thf('79',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('80',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k2_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['61','80'])).

thf('82',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['71','76'])).

thf('84',plain,
    ( ( k1_tarski @ sk_A )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['71','76'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference('sup+',[status(thm)],['84','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('92',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['81','92'])).

thf('94',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ sk_B )
    = sk_B ),
    inference('sup+',[status(thm)],['10','93'])).

thf('95',plain,(
    ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ sk_B ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('97',plain,(
    ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ sk_B )
 != sk_B ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['94','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yullXjLzlN
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:35:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.62  % Solved by: fo/fo7.sh
% 0.39/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.62  % done 563 iterations in 0.167s
% 0.39/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.62  % SZS output start Refutation
% 0.39/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.39/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.62  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.39/0.62  thf(t140_zfmisc_1, conjecture,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( r2_hidden @ A @ B ) =>
% 0.39/0.62       ( ( k2_xboole_0 @
% 0.39/0.62           ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.39/0.62         ( B ) ) ))).
% 0.39/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.62    (~( ![A:$i,B:$i]:
% 0.39/0.62        ( ( r2_hidden @ A @ B ) =>
% 0.39/0.62          ( ( k2_xboole_0 @
% 0.39/0.62              ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.39/0.62            ( B ) ) ) )),
% 0.39/0.62    inference('cnf.neg', [status(esa)], [t140_zfmisc_1])).
% 0.39/0.62  thf('0', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(l1_zfmisc_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.39/0.62  thf('1', plain,
% 0.39/0.62      (![X38 : $i, X40 : $i]:
% 0.39/0.62         ((r1_tarski @ (k1_tarski @ X38) @ X40) | ~ (r2_hidden @ X38 @ X40))),
% 0.39/0.62      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.39/0.62  thf('2', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.39/0.62      inference('sup-', [status(thm)], ['0', '1'])).
% 0.39/0.62  thf(t28_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.39/0.62  thf('3', plain,
% 0.39/0.62      (![X13 : $i, X14 : $i]:
% 0.39/0.62         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.39/0.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.39/0.62  thf('4', plain,
% 0.39/0.62      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.62  thf(commutativity_k3_xboole_0, axiom,
% 0.39/0.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.39/0.62  thf('5', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.39/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.39/0.62  thf('6', plain,
% 0.39/0.62      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['4', '5'])).
% 0.39/0.62  thf(t48_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.39/0.62  thf('7', plain,
% 0.39/0.62      (![X20 : $i, X21 : $i]:
% 0.39/0.62         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.39/0.62           = (k3_xboole_0 @ X20 @ X21))),
% 0.39/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.62  thf(t39_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.39/0.62  thf('8', plain,
% 0.39/0.62      (![X18 : $i, X19 : $i]:
% 0.39/0.62         ((k2_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18))
% 0.39/0.62           = (k2_xboole_0 @ X18 @ X19))),
% 0.39/0.62      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.39/0.62  thf('9', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.39/0.62           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.39/0.62      inference('sup+', [status(thm)], ['7', '8'])).
% 0.39/0.62  thf('10', plain,
% 0.39/0.62      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.39/0.62         (k1_tarski @ sk_A))
% 0.39/0.62         = (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ sk_B))),
% 0.39/0.62      inference('sup+', [status(thm)], ['6', '9'])).
% 0.39/0.62  thf(d10_xboole_0, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.39/0.62  thf('11', plain,
% 0.39/0.62      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.39/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.62  thf('12', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.39/0.62      inference('simplify', [status(thm)], ['11'])).
% 0.39/0.62  thf('13', plain,
% 0.39/0.62      (![X13 : $i, X14 : $i]:
% 0.39/0.62         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.39/0.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.39/0.62  thf('14', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['12', '13'])).
% 0.39/0.62  thf('15', plain,
% 0.39/0.62      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['4', '5'])).
% 0.39/0.62  thf(t112_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 0.39/0.62       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 0.39/0.62  thf('16', plain,
% 0.39/0.62      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.39/0.62         ((k5_xboole_0 @ (k3_xboole_0 @ X10 @ X12) @ (k3_xboole_0 @ X11 @ X12))
% 0.39/0.62           = (k3_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ X12))),
% 0.39/0.62      inference('cnf', [status(esa)], [t112_xboole_1])).
% 0.39/0.62  thf('17', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((k5_xboole_0 @ (k3_xboole_0 @ X0 @ (k1_tarski @ sk_A)) @ 
% 0.39/0.62           (k1_tarski @ sk_A))
% 0.39/0.62           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['15', '16'])).
% 0.39/0.62  thf('18', plain,
% 0.39/0.62      (((k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.39/0.62         = (k3_xboole_0 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.39/0.62            (k1_tarski @ sk_A)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['14', '17'])).
% 0.39/0.62  thf('19', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['12', '13'])).
% 0.39/0.62  thf(t100_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.39/0.62  thf('20', plain,
% 0.39/0.62      (![X8 : $i, X9 : $i]:
% 0.39/0.62         ((k4_xboole_0 @ X8 @ X9)
% 0.39/0.62           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.39/0.62  thf('21', plain,
% 0.39/0.62      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.39/0.62      inference('sup+', [status(thm)], ['19', '20'])).
% 0.39/0.62  thf('22', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.39/0.62      inference('simplify', [status(thm)], ['11'])).
% 0.39/0.62  thf(l32_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.39/0.62  thf('23', plain,
% 0.39/0.62      (![X5 : $i, X7 : $i]:
% 0.39/0.62         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.39/0.62      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.39/0.62  thf('24', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['22', '23'])).
% 0.39/0.62  thf('25', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.39/0.62      inference('demod', [status(thm)], ['21', '24'])).
% 0.39/0.62  thf('26', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.39/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.39/0.62  thf('27', plain,
% 0.39/0.62      (((k1_xboole_0)
% 0.39/0.62         = (k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.39/0.62            (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.39/0.62      inference('demod', [status(thm)], ['18', '25', '26'])).
% 0.39/0.62  thf('28', plain,
% 0.39/0.62      (![X20 : $i, X21 : $i]:
% 0.39/0.62         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.39/0.62           = (k3_xboole_0 @ X20 @ X21))),
% 0.39/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.62  thf('29', plain,
% 0.39/0.62      (![X20 : $i, X21 : $i]:
% 0.39/0.62         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.39/0.62           = (k3_xboole_0 @ X20 @ X21))),
% 0.39/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.62  thf('30', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.39/0.62           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['28', '29'])).
% 0.39/0.62  thf(t36_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.39/0.62  thf('31', plain,
% 0.39/0.62      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 0.39/0.62      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.39/0.62  thf('32', plain,
% 0.39/0.62      (![X13 : $i, X14 : $i]:
% 0.39/0.62         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.39/0.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.39/0.62  thf('33', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.39/0.62           = (k4_xboole_0 @ X0 @ X1))),
% 0.39/0.62      inference('sup-', [status(thm)], ['31', '32'])).
% 0.39/0.62  thf('34', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.39/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.39/0.62  thf('35', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.39/0.62           = (k4_xboole_0 @ X0 @ X1))),
% 0.39/0.62      inference('demod', [status(thm)], ['33', '34'])).
% 0.39/0.62  thf('36', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.39/0.62           = (k4_xboole_0 @ X1 @ X0))),
% 0.39/0.62      inference('demod', [status(thm)], ['30', '35'])).
% 0.39/0.62  thf('37', plain,
% 0.39/0.62      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)
% 0.39/0.62         = (k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.39/0.62            (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['27', '36'])).
% 0.39/0.62  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.39/0.62  thf('38', plain, (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ X15)),
% 0.39/0.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.39/0.62  thf('39', plain,
% 0.39/0.62      (![X13 : $i, X14 : $i]:
% 0.39/0.62         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.39/0.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.39/0.62  thf('40', plain,
% 0.39/0.62      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['38', '39'])).
% 0.39/0.62  thf('41', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.39/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.39/0.62  thf('42', plain,
% 0.39/0.62      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.62      inference('sup+', [status(thm)], ['40', '41'])).
% 0.39/0.62  thf('43', plain,
% 0.39/0.62      (![X8 : $i, X9 : $i]:
% 0.39/0.62         ((k4_xboole_0 @ X8 @ X9)
% 0.39/0.62           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.39/0.62  thf('44', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.39/0.62      inference('sup+', [status(thm)], ['42', '43'])).
% 0.39/0.62  thf(t5_boole, axiom,
% 0.39/0.62    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.39/0.62  thf('45', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.39/0.62      inference('cnf', [status(esa)], [t5_boole])).
% 0.39/0.62  thf('46', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.39/0.62      inference('sup+', [status(thm)], ['44', '45'])).
% 0.39/0.62  thf('47', plain,
% 0.39/0.62      (((k1_tarski @ sk_A)
% 0.39/0.62         = (k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.39/0.62            (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.39/0.62      inference('demod', [status(thm)], ['37', '46'])).
% 0.39/0.62  thf('48', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.39/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.39/0.62  thf(t94_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( k2_xboole_0 @ A @ B ) =
% 0.39/0.62       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.39/0.62  thf('49', plain,
% 0.39/0.62      (![X26 : $i, X27 : $i]:
% 0.39/0.62         ((k2_xboole_0 @ X26 @ X27)
% 0.39/0.62           = (k5_xboole_0 @ (k5_xboole_0 @ X26 @ X27) @ 
% 0.39/0.62              (k3_xboole_0 @ X26 @ X27)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.39/0.62  thf(t91_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.39/0.62       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.39/0.62  thf('50', plain,
% 0.39/0.62      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.39/0.62         ((k5_xboole_0 @ (k5_xboole_0 @ X23 @ X24) @ X25)
% 0.39/0.62           = (k5_xboole_0 @ X23 @ (k5_xboole_0 @ X24 @ X25)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.39/0.62  thf('51', plain,
% 0.39/0.62      (![X26 : $i, X27 : $i]:
% 0.39/0.62         ((k2_xboole_0 @ X26 @ X27)
% 0.39/0.62           = (k5_xboole_0 @ X26 @ 
% 0.39/0.62              (k5_xboole_0 @ X27 @ (k3_xboole_0 @ X26 @ X27))))),
% 0.39/0.62      inference('demod', [status(thm)], ['49', '50'])).
% 0.39/0.62  thf('52', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((k2_xboole_0 @ X0 @ X1)
% 0.39/0.62           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.39/0.62      inference('sup+', [status(thm)], ['48', '51'])).
% 0.39/0.62  thf('53', plain,
% 0.39/0.62      (![X8 : $i, X9 : $i]:
% 0.39/0.62         ((k4_xboole_0 @ X8 @ X9)
% 0.39/0.62           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.39/0.62  thf('54', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((k2_xboole_0 @ X0 @ X1)
% 0.39/0.62           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.39/0.62      inference('demod', [status(thm)], ['52', '53'])).
% 0.39/0.62  thf('55', plain,
% 0.39/0.62      (((k2_xboole_0 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.39/0.62         (k1_tarski @ sk_A))
% 0.39/0.62         = (k5_xboole_0 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.39/0.62            (k1_tarski @ sk_A)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['47', '54'])).
% 0.39/0.62  thf('56', plain,
% 0.39/0.62      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.39/0.62         ((k5_xboole_0 @ (k5_xboole_0 @ X23 @ X24) @ X25)
% 0.39/0.62           = (k5_xboole_0 @ X23 @ (k5_xboole_0 @ X24 @ X25)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.39/0.62  thf('57', plain,
% 0.39/0.62      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['4', '5'])).
% 0.39/0.62  thf('58', plain,
% 0.39/0.62      (![X8 : $i, X9 : $i]:
% 0.39/0.62         ((k4_xboole_0 @ X8 @ X9)
% 0.39/0.62           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.39/0.62  thf('59', plain,
% 0.39/0.62      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.39/0.62         = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['57', '58'])).
% 0.39/0.62  thf('60', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((k2_xboole_0 @ X0 @ X1)
% 0.39/0.62           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.39/0.62      inference('demod', [status(thm)], ['52', '53'])).
% 0.39/0.62  thf('61', plain,
% 0.39/0.62      (((k2_xboole_0 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.39/0.62         (k1_tarski @ sk_A)) = (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.39/0.62      inference('demod', [status(thm)], ['55', '56', '59', '60'])).
% 0.39/0.62  thf('62', plain,
% 0.39/0.62      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.39/0.62         = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['57', '58'])).
% 0.39/0.62  thf('63', plain,
% 0.39/0.62      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.39/0.62         ((k5_xboole_0 @ (k5_xboole_0 @ X23 @ X24) @ X25)
% 0.39/0.62           = (k5_xboole_0 @ X23 @ (k5_xboole_0 @ X24 @ X25)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.39/0.62  thf('64', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.39/0.62      inference('demod', [status(thm)], ['21', '24'])).
% 0.39/0.62  thf('65', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((k1_xboole_0)
% 0.39/0.62           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 0.39/0.62      inference('sup+', [status(thm)], ['63', '64'])).
% 0.39/0.62  thf('66', plain,
% 0.39/0.62      (((k1_xboole_0)
% 0.39/0.62         = (k5_xboole_0 @ sk_B @ 
% 0.39/0.62            (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.39/0.62             (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.39/0.62      inference('sup+', [status(thm)], ['62', '65'])).
% 0.39/0.62  thf('67', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((k2_xboole_0 @ X0 @ X1)
% 0.39/0.62           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.39/0.62      inference('demod', [status(thm)], ['52', '53'])).
% 0.39/0.62  thf('68', plain,
% 0.39/0.62      (((k1_xboole_0)
% 0.39/0.62         = (k5_xboole_0 @ sk_B @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.39/0.62      inference('demod', [status(thm)], ['66', '67'])).
% 0.39/0.62  thf('69', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.39/0.62      inference('demod', [status(thm)], ['21', '24'])).
% 0.39/0.62  thf('70', plain,
% 0.39/0.62      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.39/0.62         ((k5_xboole_0 @ (k5_xboole_0 @ X23 @ X24) @ X25)
% 0.39/0.62           = (k5_xboole_0 @ X23 @ (k5_xboole_0 @ X24 @ X25)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.39/0.62  thf('71', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.39/0.62           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['69', '70'])).
% 0.39/0.62  thf('72', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.39/0.62      inference('demod', [status(thm)], ['21', '24'])).
% 0.39/0.62  thf('73', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.39/0.62           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['69', '70'])).
% 0.39/0.62  thf('74', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.39/0.62      inference('sup+', [status(thm)], ['72', '73'])).
% 0.39/0.62  thf('75', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.39/0.62      inference('cnf', [status(esa)], [t5_boole])).
% 0.39/0.62  thf('76', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.39/0.62      inference('demod', [status(thm)], ['74', '75'])).
% 0.39/0.62  thf('77', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.39/0.62      inference('demod', [status(thm)], ['71', '76'])).
% 0.39/0.62  thf('78', plain,
% 0.39/0.62      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.39/0.62         = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.39/0.62      inference('sup+', [status(thm)], ['68', '77'])).
% 0.39/0.62  thf('79', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.39/0.62      inference('cnf', [status(esa)], [t5_boole])).
% 0.39/0.62  thf('80', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B))),
% 0.39/0.62      inference('demod', [status(thm)], ['78', '79'])).
% 0.39/0.62  thf('81', plain,
% 0.39/0.62      (((k2_xboole_0 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.39/0.62         (k1_tarski @ sk_A)) = (sk_B))),
% 0.39/0.62      inference('demod', [status(thm)], ['61', '80'])).
% 0.39/0.62  thf('82', plain,
% 0.39/0.62      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.39/0.62         = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['57', '58'])).
% 0.39/0.62  thf('83', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.39/0.62      inference('demod', [status(thm)], ['71', '76'])).
% 0.39/0.62  thf('84', plain,
% 0.39/0.62      (((k1_tarski @ sk_A)
% 0.39/0.62         = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.39/0.62      inference('sup+', [status(thm)], ['82', '83'])).
% 0.39/0.62  thf('85', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((k1_xboole_0)
% 0.39/0.62           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 0.39/0.62      inference('sup+', [status(thm)], ['63', '64'])).
% 0.39/0.62  thf('86', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.39/0.62      inference('demod', [status(thm)], ['71', '76'])).
% 0.39/0.62  thf('87', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 0.39/0.62           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.39/0.62      inference('sup+', [status(thm)], ['85', '86'])).
% 0.39/0.62  thf('88', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.39/0.62      inference('cnf', [status(esa)], [t5_boole])).
% 0.39/0.62  thf('89', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 0.39/0.63      inference('demod', [status(thm)], ['87', '88'])).
% 0.39/0.63  thf('90', plain,
% 0.39/0.63      (((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.39/0.63         (k1_tarski @ sk_A)) = (sk_B))),
% 0.39/0.63      inference('sup+', [status(thm)], ['84', '89'])).
% 0.39/0.63  thf('91', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]:
% 0.39/0.63         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 0.39/0.63      inference('demod', [status(thm)], ['87', '88'])).
% 0.39/0.63  thf('92', plain,
% 0.39/0.63      (((k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.39/0.63         = (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.39/0.63      inference('sup+', [status(thm)], ['90', '91'])).
% 0.39/0.63  thf('93', plain,
% 0.39/0.63      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.39/0.63         (k1_tarski @ sk_A)) = (sk_B))),
% 0.39/0.63      inference('demod', [status(thm)], ['81', '92'])).
% 0.39/0.63  thf('94', plain,
% 0.39/0.63      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ sk_B)
% 0.39/0.63         = (sk_B))),
% 0.39/0.63      inference('sup+', [status(thm)], ['10', '93'])).
% 0.39/0.63  thf('95', plain,
% 0.39/0.63      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.39/0.63         (k1_tarski @ sk_A)) != (sk_B))),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('96', plain,
% 0.39/0.63      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.39/0.63         (k1_tarski @ sk_A))
% 0.39/0.63         = (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ sk_B))),
% 0.39/0.63      inference('sup+', [status(thm)], ['6', '9'])).
% 0.39/0.63  thf('97', plain,
% 0.39/0.63      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ sk_B)
% 0.39/0.63         != (sk_B))),
% 0.39/0.63      inference('demod', [status(thm)], ['95', '96'])).
% 0.39/0.63  thf('98', plain, ($false),
% 0.39/0.63      inference('simplify_reflect-', [status(thm)], ['94', '97'])).
% 0.39/0.63  
% 0.39/0.63  % SZS output end Refutation
% 0.39/0.63  
% 0.50/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
